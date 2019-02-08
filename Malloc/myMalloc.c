#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

//static header * freelist;
// start of memory pool
static void *mem_start;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
	if (raw_size <= 0)
		return NULL;	
	if (raw_size < MIN_ALLOCATION)
		raw_size = MIN_ALLOCATION;
	// round up the allocated block size to 8-byte modulo
	size_t rounded_size;
	rounded_size = (raw_size + ALLOC_HEADER_SIZE + 7) & (-8);
	if ((raw_size + ALLOC_HEADER_SIZE) <= 32)
    rounded_size = 32;
	int index = (rounded_size - ALLOC_HEADER_SIZE) / 8 - 1;
//	rounded_size += ALLOC_HEADER_SIZE;

	if (index >= N_LISTS) {
		index = N_LISTS - 1;
	}

	// traverse the freelistSentinels to find if it can be inserted a block
	int insert = 0;
	header * block;
	for (index; index < N_LISTS-1; index++) {
		header * current = &freelistSentinels[index];
		if (get_size(current->next) >= rounded_size) {
			insert = 1;
			block = current->next;
			break;
		}	
	}
	if (insert == 0) {
		header * current = &freelistSentinels[index];
		header * start = current;
		do {
			current = current->next;
			if (get_size(current) >= rounded_size) {
      	insert = 1;
      	block = current;
      	break;
    	}	
		}while(current != start);
	}

	// when the user request can be fufilled with the available block 
	if (insert == 1) {
		size_t size_offset = get_size(block) - rounded_size;
	// when the block is the right size or the leftover isn't big enough to be allocated
		if (size_offset >= 0 && size_offset < 32) {
			header * right_head = get_right_header(block);
			set_state(block, ALLOCATED);
			right_head->left_size = get_size(block);
			block->next->prev = block->prev;
			block->prev->next = block->next;
			
			return (void *)&block->data[0];
		} else {
	// when the leftover is large enough to be allocated, split the block into two samller blocks
			header * new = get_header_from_offset(block, size_offset); 
			set_size(new, rounded_size);
			set_size(block, size_offset);
			set_state(new, ALLOCATED);
			new->left_size = size_offset;
			header * right_head = get_right_header(new);
			right_head -> left_size = get_size(new);

	// just in case the block has already been inserted
			int j = (get_size(block) - ALLOC_HEADER_SIZE) / 8 - 1;
			if(j >= N_LISTS) { 
				j = N_LISTS - 1;
			}
			if (j == index) {		
				return (void *)&new->data[0];
			} else {
				block->next->prev = block->prev;
        block->prev->next = block->next;
        header * sentinel = &freelistSentinels[j];
        block->next = sentinel->next;
        block->prev = sentinel;
        sentinel->next->prev = block;
        sentinel->next = block;	
			
				return (void *)&new->data[0];
			}
		}
	// there is no block fixed in the freelistSentinels, we need to add a new chunk
	} else {
		header * new_chunk = allocate_chunk(ARENA_SIZE);
		header * fence = get_header_from_offset(new_chunk, -ALLOC_HEADER_SIZE);
		lastFencePost = get_header_from_offset(new_chunk, get_size(new_chunk));
		header * left_head = get_left_header(new_chunk);
		header * ll_head = get_left_header(left_head);
		int size_l = get_size(left_head);
		int size_ll = get_size(ll_head);
		
	// when the new chunk is adjacent to the previous chunk
		if (get_state(ll_head) == FENCEPOST && get_state(left_head) == FENCEPOST) {
			header * lll_head = get_left_header(ll_head);

			if (get_state(lll_head) == UNALLOCATED) {	
				set_size(lll_head, get_size(lll_head) + 2*ALLOC_HEADER_SIZE + get_size(new_chunk));
				lastFencePost = get_right_header(new_chunk);
				lastFencePost->left_size = get_size(lll_head);
				int k  = (get_size(lll_head) - ALLOC_HEADER_SIZE) / 8 - 1;
				if (k >= N_LISTS) {
					k = N_LISTS - 1;
				}
				lll_head->next->prev = lll_head->prev;
				lll_head->prev->next = lll_head->next;
				
				header * sentinel1 = &freelistSentinels[k];
				lll_head->next = sentinel1->next;
				lll_head->prev = sentinel1->prev;
				sentinel1->next->prev = lll_head;
				sentinel1->next = lll_head;

				return allocate_object(raw_size);
			} else {
				set_size(ll_head, 2*ALLOC_HEADER_SIZE + get_size(new_chunk));
				set_state(ll_head, UNALLOCATED);
				lastFencePost->left_size = get_size(new_chunk) + 2*ALLOC_HEADER_SIZE;
				int l = (get_size(ll_head) - ALLOC_HEADER_SIZE) / 8 - 1;
				if (l >= N_LISTS) {
          l = N_LISTS - 1;
        }
				header * sentinel2 = &freelistSentinels[l];
				ll_head->next = sentinel2->next;
       	ll_head->prev = sentinel2->prev;
       	sentinel2->next->prev = ll_head;
       	sentinel2->next = ll_head;		
				return allocate_object(raw_size);

	// when the new block is not adjacent to the previous chunk, add the new chunk 
			}
		} else {
			insert_os_chunk(fence);
			header * sentinel3 = &freelistSentinels[N_LISTS - 1];
      new_chunk->next = sentinel3->next;
      new_chunk->prev = sentinel3->prev;
      sentinel3->next->prev = new_chunk;
      sentinel3->next = new_chunk;

      return allocate_object(raw_size);

		}	
	}
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
	if (p == NULL) {
		return;
	}
	header * p_header = ptr_to_header(p);
	if (get_state(p_header) == UNALLOCATED) {
		printf("Double Free Detected\n");
		assert(false);
		exit(1);
	}
	size_t index = (get_size(p_header) - ALLOC_HEADER_SIZE) / 8 - 1;
	
	if (index >= N_LISTS) 
		index = N_LISTS - 1;	
	header * location = &freelistSentinels[index];
	header * left_header = get_left_header(p_header);
	header * right_header = get_right_header(p_header);

	// if the adjacent blocks are allocated
	if (get_state(left_header) != UNALLOCATED && get_state(right_header) != UNALLOCATED) {
		set_state(p_header, UNALLOCATED);
		p_header->prev = location;
		p_header->next = location->next;
		location->next->prev = p_header;
		location->next = p_header;
	// if the right block is unallocated
	} else if (get_state(right_header) == UNALLOCATED && get_state(left_header) != UNALLOCATED) {
		set_state(p_header, UNALLOCATED);
		size_t r = (get_size(right_header) - ALLOC_HEADER_SIZE) / 8 - 1;
	// put the new block in the right location
		set_size(p_header, get_size(p_header) + get_size(right_header));
		size_t i = (get_size(p_header) - ALLOC_HEADER_SIZE) / 8 - 1;
		if( i >= N_LISTS)
			i = N_LISTS - 1; 
		if ( r >= N_LISTS)
			r = N_LISTS - 1;
		header * rr_header = get_right_header(right_header);
		rr_header->left_size= get_size(p_header);
		right_header->next->prev = p_header;
    right_header->prev->next = p_header;
		p_header->next = right_header->next;
		p_header->prev = right_header->prev;
    right_header->next->prev = right_header->prev;
    right_header->prev->next = right_header->next;

		if (i == r){
			return;
		}
		else {
			p_header->prev->next = p_header->next;
			p_header->next->prev = p_header->prev;
			header * location1 = &freelistSentinels[i];
			p_header->next = location1->next;
			p_header->prev = location1;
			location1->next->prev = p_header;
			location1->next = p_header;
		}
	// if the left header is unallocated
	} else if (get_state(left_header) == UNALLOCATED && get_state(right_header) != UNALLOCATED) {
		set_state(p_header, UNALLOCATED);
	// get the location of the left header
		size_t j = (get_size(left_header) - ALLOC_HEADER_SIZE) / 8 - 1;
		set_size(left_header, get_size(left_header) + get_size(p_header));
		right_header->left_size = get_size(left_header);
		size_t k = (get_size(left_header) - ALLOC_HEADER_SIZE) / 8 - 1;
		if (k >= N_LISTS)
			k = N_LISTS-1;
		if (j >= N_LISTS) 
          j = N_LISTS - 1;
		
		if (j == k) 
			return;
		else {
			left_header->next->prev = left_header->prev;
      left_header->prev->next = left_header->next;
  
	    header * location2 = &freelistSentinels[k];
      left_header->next = location2->next;
      left_header->prev = location2;
      location2->next->prev = left_header;
      location2->next = left_header;
		}
	// if the adjacent blocks are unallocated
	} else {
		set_state(p_header, UNALLOCATED);
	// get the location of the left header
    int s = (get_size(left_header) - ALLOC_HEADER_SIZE) / 8 - 1;
    set_size(left_header, get_size(left_header) + get_size(p_header) + get_size(right_header));
		header * rr_header = get_right_header(right_header);
    rr_header->left_size = get_size(left_header);
    int t = (get_size(left_header) - ALLOC_HEADER_SIZE) / 8 - 1;

		if (t >= N_LISTS)
      t = N_LISTS-1;
		if (s >= N_LISTS)
          s = N_LISTS - 1;
		if (s == t) {
			right_header->next->prev = right_header->prev;
			right_header->prev->next = right_header->next;
			return;
		} else {
			right_header->next->prev = right_header->prev;
      right_header->prev->next = right_header->next;
			left_header->next->prev = left_header->prev;
      left_header->prev->next = left_header->next;

			header * location3 = &freelistSentinels[t];
			left_header->next = location3->next;
      left_header->prev = location3;
      location3->next->prev = left_header;
      location3->next = left_header;
		}
	}
		
 // (void) p;
 // assert(false);
 // exit(1);
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */

static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
	mem_start = (char *) block;

//	_initialized = 1;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
