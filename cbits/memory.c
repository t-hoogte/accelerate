#include <inttypes.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdatomic.h>

#include "align.h"
#include "flags.h"

struct ObjectHeader {
  uint64_t reference_count;
  uint64_t byte_size;
} CACHE_ALIGNED;

void* accelerate_buffer_alloc(uint64_t byte_size) {
  void* ptr = aligned_alloc(CACHE_LINE_SIZE, byte_size + sizeof(struct ObjectHeader));
  // TODO: call ___tracy_emit_memory_alloc

  struct ObjectHeader* header = (struct ObjectHeader*) ptr;
  header->reference_count = 1;
  header->byte_size = byte_size;

  void* interior = ptr + sizeof(struct ObjectHeader);
  return interior;
}

uint64_t accelerate_buffer_byte_size(void* interior) {
  struct ObjectHeader* header = (struct ObjectHeader*) (interior - sizeof(struct ObjectHeader));
  return header->byte_size;
}

void accelerate_buffer_retain(void* interior) {
  struct ObjectHeader* header = (struct ObjectHeader*) (interior - sizeof(struct ObjectHeader));
  atomic_fetch_add_explicit(&header->reference_count, 1, memory_order_acquire);
}

void accelerate_buffer_release(void* interior) {
  struct ObjectHeader* header = (struct ObjectHeader*) (interior - sizeof(struct ObjectHeader));
  // Release is always needed, acquire only when the reference count drops to zero.
  int old = atomic_fetch_add_explicit(&header->reference_count, 1, memory_order_acq_rel);
  if (old == 1) {
    // TODO: call ___tracy_emit_memory_free
    free(header);
  }
}
