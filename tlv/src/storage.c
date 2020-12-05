/* This is the body of the storage manager */

#include <stdio.h>
#include <sys/types.h>
#include <storage.h>

#if SYSTEM==cyg
#include <string.h>
#else
/* Needed for bcopy. */
#include <strings.h>
#endif

/* This is actually 2^16 or 65536. */
#define ALLOCSIZE (2<<15)

/* If this is defined then dont use sbrk - use malloc only. */
#define NOSBRK 1

#ifdef NOSBRK

#include <stdlib.h>

void init_storage(){}  /* Do no initialization. */

static int memory_allocated = 0 ;
unsigned int get_bytes_allocated(void)
{
 return memory_allocated;
}

#else

static char *addrlimit;
static char *addrfree;

/* needed for calculating the amount of memory allocated so far. */
static char* addrstart;

/* this routine initializes the storage manager */
void init_storage()
{
#ifdef MACH
  mach_init();		/* needed to make sbrk() work */
#endif
  /* addrfree points to the first free byte
     addrlimit points to the memory limit */
    addrfree = addrlimit = (char *) sbrk(0);

  addrstart = (char *) sbrk(0);    
}

/* Thie routine returns the amount of memory allocated so far */
unsigned int get_bytes_allocated(void)
{
 return ((unsigned)((char *)sbrk(0)-addrstart));
}

void alloc_fail(int alimit, int na)
{
  fprintf(stderr,"Failed to allocate %d bytes: addrlimit = %xH, na = %xH\n",
         ALLOCSIZE,alimit,na);
  exit(1);
}

/* get ALLOCSIZE more bytes from the O.S. */
static void getmore(void)
{
  char *na;
/*  fprintf(stderr,"Getting %d more bytes\n",ALLOCSIZE); */
  if(addrlimit != (char *)sbrk(0)){ /* in case someone else did sbrk */
    sbrk((4 - (sbrk(0) % 4)) % 4);
    addrfree = addrlimit = (char *)sbrk(0);
    if(((unsigned)addrlimit) % 4 != 0)
      alloc_fail((int)addrlimit,(int)na);
  }
  if((na = (char *)sbrk(ALLOCSIZE)) != addrlimit)
      alloc_fail((int)addrlimit,(int)na);

  addrlimit += ALLOCSIZE;
}


/*----------------------------------------------------------------------*/

/* provide malloc for miscellaneuos storage allocation */
/* Was once called malloc */
static char *storage_malloc(int n)
{
  if(n % 4)n=n+4-(n%4);  /* always allocate multiple of four bytes */
  while(addrfree + n > addrlimit)getmore();
  {
    char *r = addrfree;
    addrfree += n;
    return(r);
  }
}

/* very simple implementation of free */
static void storage_free(char *p)
{
  return;
}

/*----------------------------------------------------------------------*/

#endif

/* initialize a record manager.
   sets the free list to NULL,
   and makes sure the record size
   is at least big enough for a pointer */

mgr_ptr new_mgr(int rec_size)
{
  /* Allocate memory for new record manager */
#ifdef NOSBRK
  register mgr_ptr mp = (mgr_ptr)malloc(sizeof(struct mgr));
  memory_allocated += sizeof(struct mgr);
#else
  register mgr_ptr mp = (mgr_ptr)storage_malloc(sizeof(struct mgr));
#endif

  /* Initialize fields of record manager */
  mp->free.link = 0;
  mp->rec_size = rec_size;
  mp->count = 0;
  mp->free_hook = 0;
  return(mp);
}


void print_free_list(mgr_ptr mp)
{
  rec_ptr r = mp->free.link;
  rec_ptr last;
  fprintf(stderr,"Free list: Start %d ",(int)r);
  while (r) 
    {
     last = r;
     r = r->link;
    }

  fprintf(stderr,"End %d\n",(int)last);
}


/* get a new record. if the free list
   is not empty, pull the first record off this
   list. else get ALLOCSIZE more bytes and
   make a new block of records. Link all
   of these record into a free list.
   then get the first element of this list
   by calling new_rec recursively. */

rec_ptr new_rec(register mgr_ptr mp)
{
  register rec_ptr p1;

  if(mp->free.link){
    /* Return a record from the free list */
    rec_ptr r = mp->free.link;
    mp->free.link = (mp->free.link)->link;
    r->link = 0;
    return(r);
  }
  /* Get more memory */
  {
#ifdef NOSBRK

  static char *addrlimit;
  static char *addrfree;

  /* For debugging: static i = 0;
  i++; fprintf(stderr,"Malloc # %d\n",i);*/

  if ((addrfree = (char *)malloc(ALLOCSIZE)) == NULL)
    {
      fprintf(stderr,"Malloc failed!!");
    }
  addrlimit = addrfree + ALLOCSIZE;
  memory_allocated += ALLOCSIZE;
#else
  getmore();
#endif

  p1 = &(mp->free);
  /* Break the memory up and fill the free list.
     This is done by going over the array and assigning
     the "link" field to the next address. */
  while(addrlimit-addrfree >= mp->rec_size){
    p1->link = (rec_ptr)addrfree;
    p1 = (rec_ptr)addrfree;
    addrfree += mp->rec_size;
  }
  p1->link=0; /* Terminate the linked list */
  }

  /*  print_free_list(mp);*/

  /* Call new_rec recursively to return a record */
  return(new_rec(mp));
}

/* put a record on the free list */
void free_rec(register mgr_ptr mp, rec_ptr r)
{
  register rec_ptr rp = r;
  if (mp->free_hook)
    (*(mp->free_hook))(rp);
  rp->link = mp->free.link;
  mp->free.link = rp;
}

/* Get a new record which is a duplicate of an existing record */
rec_ptr dup_rec(mgr_ptr mp, rec_ptr r)
{
  register rec_ptr res = new_rec(mp);

#if SYSTEM==cyg
  memcpy(res,r,mp->rec_size);
#else
  bcopy(r,res,mp->rec_size);
#endif
  res->link = 0;
  return(res);
}

