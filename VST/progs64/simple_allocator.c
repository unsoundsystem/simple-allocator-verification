#include <stddef.h>
#include <stdint.h>

#define CHUNK_SIZE 1024
#define ENTRY_SIZE 4

unsigned char _space[CHUNK_SIZE];

struct slab {
    size_t chunksize; // size can be allocated remain
    size_t entry_size; // size of objects
    unsigned char *chunk; // pointer to the next free chunk
};

void slab_init(struct slab *s)
{
    s->chunk = (void *)&_space;
    s->chunksize = CHUNK_SIZE;
    s->entry_size = ENTRY_SIZE;
}

void* slab_alloc(struct slab *s)
{
    void* r;
	if (s->entry_size > s->chunksize) {
		return NULL;
	} else {
		r = s->chunk;
		s->chunk = s->chunk + s->entry_size;
		s->chunksize = s->chunksize - s->entry_size;
		return r;
	}
}

struct slab four_bytes_allocator;
int main(void) {
	slab_init(&four_bytes_allocator);
	char *c1 = slab_alloc(&four_bytes_allocator);
	char *c2 = slab_alloc(&four_bytes_allocator);
	char *c3 = slab_alloc(&four_bytes_allocator);
	*c1 = 1;
	//*_i ci \mapsto - を示す
}
