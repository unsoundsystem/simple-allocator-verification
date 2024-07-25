#include <stddef.h>
#include <stdint.h>

typedef struct freelist {
    struct freelist *next;
} *freelist_t;

struct slab {
    size_t chunksize;
    size_t entry_size; // size of objects
    unsigned char *chunk;
    freelist_t free; // deallocated objects
};

void slab_init(struct slab *s, unsigned char *p, size_t chunksize, size_t entry_size)
{
    s->chunk = p;
    s->chunksize = chunksize;
    s->entry_size = entry_size;
    s->free = NULL;
}

void* slab_alloc(struct slab *s)
{
    struct freelist *f;
    void* r;
    if (s->free != NULL) {
        f = s->free;
        s->free = f->next;
        r = f;
        return r;
    } else {
        if (s->entry_size > s->chunksize) {
            return NULL;
        } else {
            r = s->chunk;
            s->chunk = s->chunk + s->entry_size;
            s->chunksize = s->chunksize - s->entry_size;
            return r;
        }
    }
}

void slab_free(struct slab *s, void* x)
{
    struct freelist* f = x;

    f->next = s->free;
    s->free = f;
}

unsigned char _space[1024];
struct slab four_bytes_allocator;
int main(void) {
	slab_init(&four_bytes_allocator, (unsigned char *)&_space, 1024, 4);
	char *c1 = slab_alloc(&four_bytes_allocator);
	char *c2 = slab_alloc(&four_bytes_allocator);
	char *c3 = slab_alloc(&four_bytes_allocator);
	*c1 = 1;
	//*_i ci \mapsto - を示す
	slab_free(&four_bytes_allocator, (void *)c1);
}
