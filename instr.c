// This is free and unencumbered software released into the public domain.
// For more information, see LICENSE

#include <assert.h>
#include <err.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <capstone/capstone.h>
#include <keystone/keystone.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>

#define EI_NIDENT   (16)

#define EM_X86_64   (0x3e)

#define PT_NULL     (0x00)
#define PT_LOAD     (0x01)
#define PT_DYNAMIC  (0x02)
#define PT_INTERP   (0x03)
#define PT_NOTE     (0x04)
#define PT_SHLIB    (0x05)
#define PT_PHDR     (0x06)
#define PT_TLS      (0x07)

#define SHT_NULL            (0x00)
#define SHT_PROGBITS        (0x01)
#define SHT_SYMTAB          (0x02)
#define SHT_STRTAB          (0x03)
#define SHT_RELA            (0x04)
#define SHT_HASH            (0x05)
#define SHT_DYNAMIC         (0x06)
#define SHT_NOTE            (0x07)
#define SHT_NOBITS          (0x08)
#define SHT_REL             (0x09)
#define SHT_SHLIB           (0x0a)
#define SHT_DYNSYM          (0x0b)
#define SHT_INIT_ARRAY      (0x0e)
#define SHT_FINI_ARRAY      (0x0f)
#define SHT_PREINIT_ARRAY   (0x10)
#define SHT_GROUP           (0x11)
#define SHT_SYMTAB_SHNDX    (0x12)

#define SHN_UNDEF   (0x00)

#define ELFDATA2LSB (0x01)
#define ELFCLASS64  (0x02)
#define EHMAGIC     ("\177ELF")
#define EHCLASS     (0x04)
#define EHDATA      (0x05)
#define EHVERS      (0x06)

#define PTF_EXEC  (1 << 0)
#define PTF_WRITE (1 << 1)
#define PTF_READ  (1 << 2)

#define STB_LOCAL       (0x00)
#define STB_GLIBAL      (0x01)
#define STB_WEAK        (0x02)
#define STB_NUM         (0x03)
#define STB_LOOS        (0x10)
#define STB_GNU_UNIQUE  (0x10)
#define STB_HIOS        (0x12)
#define STB_LOPROC      (0x13)
#define STB_HIPROC      (0x15)

#define STT_NOTYPE      (0x00)
#define STT_OBJECT      (0x01)
#define STT_FUNC        (0x02)
#define STT_FILE        (0x03)
#define STT_COMMON      (0x04)
#define STT_TLS         (0x05)
#define STT_NUM         (0x06)
#define STT_LOOS        (0x07)
#define STT_GNU_IFUNC   (0x10)
#define STT_HIOS        (0x10)
#define STT_LOPROC      (0x13)
#define STT_HIPROC      (0x15)

#define DT_NULL             (0x00)
#define DT_NEEDED           (0x01)
#define DT_PLTRELSZ         (0x02)
#define DT_PLTGOT           (0x03)
#define DT_HASH             (0x04)
#define DT_STRTAB           (0x05)
#define DT_SYMTAB           (0x06)
#define DT_RELA             (0x07)
#define DT_RELASZ           (0x08)
#define DT_RELAENT          (0x09)
#define DT_STRSZ            (0x0a)
#define DT_SYMENT           (0x0b)
#define DT_INIT             (0x0c)
#define DT_FINI             (0x0d)
#define DT_SONAME           (0x0e)
#define DT_RPATH            (0x0f)
#define DT_SYMBOLIC         (0x10)
#define DT_REL              (0x11)
#define DT_RELSZ            (0x12)
#define DT_RELENT           (0x13)
#define DT_PLTREL           (0x14)
#define DT_DEBUG            (0x15)
#define DT_TEXTREL          (0x16)
#define DT_JMPREL           (0x17)
#define DT_BIND_NOW         (0x18)
#define DT_INIT_ARRAY       (0x19)
#define DT_FINI_ARRAY       (0x1a)
#define DT_INIT_ARRAYSZ     (0x1b)
#define DT_FINI_ARRAYSZ     (0x1c)
#define DT_RUNPATH          (0x1d)
#define DT_FLAGS            (0x1e)
#define DT_ENCODING         (0x20)
#define DT_PREINIT_ARRAY    (0x20)
#define DT_PREINIT_ARRAYSZ  (0x21)
#define DT_NUM              (0x22)
#define DT_LOOS             (0x6000000d)
#define DT_HIOS             (0x6ffff000)
#define DT_LOPROC           (0x70000000)
#define DT_HIPROC           (0x7fffffff)
#define DT_PROCNUM          DT_MIPS_NUM

#define R_X86_64_NONE       (0x00)
#define R_X86_64_64         (0x01)
#define R_X86_64_PC32       (0x02)
#define R_X86_64_GOT32      (0x03)
#define R_X86_64_PLT32      (0x04)
#define R_X86_64_COPY       (0x05)
#define R_X86_64_GLOB_DAT   (0x06)
#define R_X86_64_JUMP_SLOT  (0x07)
#define R_X86_64_RELATIVE   (0x08)
#define R_X86_64_GOTPCREL   (0x09)

#define INSTR_MAX       (64)
#define MOVSEQ_MAX      (5)

#define NOP             (0x90)

#define __align(n)  __attribute__((aligned(n)))
#define __pack      __attribute__((packed))
#define __clean     __attribute__((cleanup(ifree)))

#define align_down(x, a) ((uintptr_t)(x) & ~((uintptr_t)(a) - 1))
#define align_up(x, a) align_down((uintptr_t)(x) + (uintptr_t)(a) - 1, a)
#define min(a, b) ((a) < (b) ? (a) : (b))
#define max(a, b) ((a) > (b) ? (a) : (b))
#define xensure(s)\
    do {\
        if ((s) == 0) {\
            breakf();\
            err(1, "%s:%d: invariant violated: "#s, __FILE__, __LINE__);\
        }\
    } while(0)
#define xensurex(s)\
    do {\
        if ((s) == 0) {\
            breakf();\
            errx(1, "invariant vilated: "#s);\
        }\
    } while(0)
#define xinbound(f, r)\
    do {\
        if ((void *)(f) < (void *)((r).beg)\
            || (void *)(f) > (void *)((r).end)) {\
            errx(1, "%d: out of bounds %s, [%s]", __LINE__, ""#f, ""#r);\
        }\
    } while (0)
#define xinrange(a, prog)\
    do {\
        xinbound((a).beg, prog);\
        xinbound((a).end, prog);\
    } while (0)

typedef uintptr_t       __elf64_addr    __align(8);
typedef unsigned long   __elf64_off     __align(8);
typedef unsigned short  __elf64_half    __align(2);
typedef unsigned        __elf64_word    __align(4);
typedef int             __elf64_sword   __align(4);
typedef unsigned long   __elf64_xword   __align(8);
typedef long            __elf64_sxword  __align(8);
typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

_Static_assert(sizeof(__elf64_addr  ) == 8, "incorrect size");
_Static_assert(sizeof(__elf64_off   ) == 8, "incorrect size");
_Static_assert(sizeof(__elf64_half  ) == 2, "incorrect size");
_Static_assert(sizeof(__elf64_word  ) == 4, "incorrect size");
_Static_assert(sizeof(__elf64_sword ) == 4, "incorrect size");
_Static_assert(sizeof(__elf64_xword ) == 8, "incorrect size");
_Static_assert(sizeof(__elf64_sxword) == 8, "incorrect size");

struct elf64_ehdr {
    unsigned char   e_ident[EI_NIDENT];
    __elf64_half    e_type;
    __elf64_half    e_machine;
    __elf64_word    e_version;
    __elf64_addr    e_entry;
    __elf64_off     e_phoff;
    __elf64_off     e_shoff;
    __elf64_word    e_flags;
    __elf64_half    e_ehsize;
    __elf64_half    e_phentsize;
    __elf64_half    e_phnum;
    __elf64_half    e_shentsize;
    __elf64_half    e_shnum;
    __elf64_half    e_shstrndx;
} __packed;

struct elf64_phdr {
    __elf64_word    p_type;
    __elf64_word    p_flags;
    __elf64_off     p_offset;
    __elf64_addr    p_vaddr;
    __elf64_addr    p_paddr;
    __elf64_xword   p_filesz;
    __elf64_xword   p_memsz;
    __elf64_xword   p_align;
} __pack;

struct elf64_shdr {
    __elf64_word    sh_name;
    __elf64_word    sh_type;
    __elf64_xword   sh_flags;
    __elf64_addr    sh_addr;
    __elf64_off     sh_offset;
    __elf64_xword   sh_size;
    __elf64_word    sh_link;
    __elf64_word    sh_info;
    __elf64_xword   sh_addralign;
    __elf64_xword   sh_entsize;
} __pack;

struct elf64_sym {
    __elf64_word    st_name;
    unsigned char   st_info;
    unsigned char   st_other;
    __elf64_half    st_shndx;
    __elf64_addr    st_value;
    __elf64_xword   st_size;
} __pack;

struct elf64_dyn {
    __elf64_xword       d_tag;
    union {
        __elf64_xword   d_val;
        __elf64_addr    d_ptr;
    };
} __pack;

struct elf64_rela {
    __elf64_addr    r_offset;
    __elf64_xword   r_info;
    __elf64_sxword  r_addend;
} __pack;

struct range {
    void *beg;
    void *end;
};

struct rangearr {
    void *beg;
    void *end;
    size_t esz;
};

enum jmpkind {
    JMP,
    JZ, JE = JZ,
    JNBE, JA = JNBE,
    JBE, JNA = JBE,
    JNZ, JNE = JNZ,
    JLE, JNG = JLE,
    JNL, JGE = JNL,
    JNLE, JG = JNLE,
    JL, JNGE = JL,
    JB, JNAE = JB, JC = JB,
    JNB, JAE = JNB, JNC = JNB,
    CALL,
    JO,
    JNO,
    JS,
    JNS,
    JP, JPE = JP,
    JNP, JPO = JNP,
    JECXZ, JRCXZ = JECXZ,
    INVALID_JMP, JMP_MAX = INVALID_JMP,
};

struct arr {
    size_t elesize;
    size_t size;
    size_t alloc;
    char data[];
};

struct str {
    size_t size;
    size_t alloc;
    char data[];
};

struct jmpinfo {
    uintptr_t from;
    uintptr_t into;
    size_t insnum;
    int len;
    enum jmpkind kind;
};

struct insinfo {
    u8 ins[INSTR_MAX];
    int len;
    char repr[64];
    u8 *pc;
};

struct segment {
    size_t off;
    size_t size;
    uintptr_t mmbeg;
    uintptr_t mmend;
};

struct insmap {
    uintptr_t oldloc;
    uintptr_t newloc;
    size_t oldlen;
    size_t insnum;
};

struct movableseq {
    int len;
    struct insmap seq[MOVSEQ_MAX];
};

static const char *const jmpstr[] = {
    [JO   ] = "jo",
    [JNO  ] = "jno",
    [JB   ] = "jb",
    [JAE  ] = "jae",
    [JE   ] = "je",
    [JNE  ] = "jne",
    [JBE  ] = "jbe",
    [JA   ] = "ja",
    [JS   ] = "js",
    [JNS  ] = "jns",
    [JP   ] = "jp",
    [JNP  ] = "jnp",
    [JL   ] = "jl",
    [JGE  ] = "jge",
    [JLE  ] = "jle",
    [JG   ] = "jg",
    [JECXZ] = "jecxz",
    [JMP  ] = "jmp",
    [CALL ] = "call"
};

static int verbose = 0;

void breakf(void) {
}

__attribute__ ((format (printf, 1, 2))) void
dbg(const char *fmt, ...) {
    if (verbose == 0) return;

    va_list vl;
    va_start(vl, fmt);
    vfprintf(stderr, fmt, vl);
    fputc('\n', stderr);
    va_end(vl);
}

void *
arr_get(struct arr *arr, size_t i) {
    return arr->data + i * arr->elesize;
}

struct arr *
arr_init(size_t elesize, size_t alloc) {
    struct arr *arr = malloc(sizeof(struct arr) + elesize * alloc);

    if (!arr) {
        return NULL;
    }
    arr->elesize = elesize;
    arr->alloc = alloc;
    arr->size = 0;
    return arr;
}

int
arr_push(struct arr **parr, const void *it) {
    struct arr *arr = *parr;

    if (arr->size == arr->alloc) {
        size_t alloc = (arr->alloc + 1) * 2;
        arr = realloc(arr, sizeof(struct arr) + arr->elesize * alloc);
        if (!arr) {
            return -1;
        }
        *parr = arr;
        arr->alloc = alloc;
    }
    memcpy(arr_get(arr, arr->size++), it, arr->elesize);
    return 0;
}

int
str_push(struct str **pstr, const void *it, size_t size) {
    struct str *str = *pstr;

    if (str->size + size > str->alloc) {
        size_t alloc = (str->alloc + size + 1) * 2;
        str = realloc(str, sizeof(struct str) + alloc);
        if (!str) {
            return -1;
        }
        *pstr = str;
        str->alloc = alloc;
    }
    memcpy(str->data + str->size, it, size);
    str->size += size;
    str->data[str->size] = 0;
    return 0;
}

struct str *
str_init(size_t alloc) {
    struct str *str = malloc(sizeof(struct str) + alloc);
    if (str == NULL) {
        return NULL;
    }
    str->alloc = alloc;
    str->size = 0;
    return str;
}

void
ifree(void *in) {
    void **pi = in;
    free(*pi);
}

int
range_resize(struct range *r, size_t size) {
    void *beg = realloc(r->beg, size);
    if (beg == NULL) {
        return -1;
    }
    r->beg = beg;
    r->end = beg + size;
    return 0;
}

char *
eat_until(char *s, char c) {
    while (*s && *s != c) s++;
    return s;
}

size_t
strlcpy(char *dest, const char *src, size_t size) {
    size_t len = strlen(src);
    if (len == 0 || size == 0) return 0;
    if (len > size - 1) len = size -1;
    memcpy(dest, src, len);
    dest[len] = 0;
    return len;
}

size_t
strnlcpy(char *dest, const char *src, size_t s, size_t size) {
    size_t len = strlen(src);
    if (len == 0 || size == 0) return 0;
    if (s > len) s = len;
    if (s > size - 1) s = size -1;
    memcpy(dest, src, s);
    dest[s] = 0;
    return s;
}

int
openf(char *fname, char **mm, size_t *mmsz) {
    int fd = open(fname, O_RDONLY);

    if (fd == -1) {
        return -1;
    }
    off_t off = lseek(fd, 0, SEEK_END);
    if (off == -1) {
        return -1;
    }
    off_t e = lseek(fd, 0, SEEK_SET);
    if (e == -1) {
        return -1;
    }
    *mmsz = off;
    if ((*mm = mmap(NULL, off, PROT_READ, MAP_PRIVATE, fd, 0)) == MAP_FAILED) {
        return -1;
    }
    return 0;
}

enum jmpkind
jmpclass(const char *str) {
    enum jmpkind ret = INVALID_JMP;

    for (size_t i = 0; i < JMP_MAX; i++) {
        if (strcmp(str, jmpstr[i]) == 0) {
            ret = i;
            break;
        }
    }
    return ret;
}

struct elf64_ehdr *
get_ehdr(struct range prog) {
    struct elf64_ehdr *eh = prog.beg;

    if (prog.beg + sizeof(struct elf64_ehdr) > prog.end) {
        errx(1, "corrupt header or not elf64 input");
    }
    if (memcmp(eh->e_ident, EHMAGIC, 4) != 0) {
        errx(1, "corrupt or not elf64 input");
    }
    if (eh->e_ident[EHCLASS] != ELFCLASS64) {
        errx(1, "wrong EHCLASS");
    }
    if (eh->e_ident[EHDATA] != ELFDATA2LSB) {
        errx(1, "wrong EHCLASS");
    }
    if (eh->e_machine != EM_X86_64) {
        errx(1, "wrong e_machine");
    }
    return eh;
}

struct range
get_sheader(struct range prog) {
    struct range sheader;
    struct elf64_ehdr *eh = get_ehdr(prog);
    sheader.beg = prog.beg + eh->e_shoff;
    sheader.end = sheader.beg + eh->e_shentsize;
    xinrange(sheader, prog);

    struct elf64_shdr *es = sheader.beg;
    if (eh->e_shnum == SHN_UNDEF) {
        sheader.end = sheader.beg + es->sh_size * eh->e_shentsize;
    } else {
        sheader.end = sheader.beg + eh->e_shnum * eh->e_shentsize;
    }
    xinrange(sheader, prog);
    return sheader;
}

struct range
get_shnames(struct range prog) {
    struct range sheader = get_sheader(prog);
    struct elf64_ehdr *eh = get_ehdr(prog);
    struct elf64_shdr *shstr = sheader.beg + eh->e_shstrndx * eh->e_shentsize;
    xinbound(shstr, prog);

    struct range shnames;
    shnames.beg = prog.beg + shstr->sh_offset;
    shnames.end = shnames.beg + shstr->sh_size;
    xinrange(shnames, prog);

    return shnames;
}

struct range
get_pheader(struct range prog) {
    struct elf64_ehdr *eh = get_ehdr(prog);
    struct range pheader;
    pheader.beg = prog.beg + eh->e_phoff;
    pheader.end = pheader.beg + eh->e_phnum * eh->e_phentsize;
    xinrange(pheader, prog);

    return pheader;
}

struct elf64_phdr *
get_phdr(struct range prog, unsigned type) {
    struct elf64_ehdr *eh = get_ehdr(prog);
    struct range pheader = get_pheader(prog);

    for (void *cur = pheader.beg; cur < pheader.end; cur += eh->e_phentsize) {
        struct elf64_phdr *ph = cur;
        if (ph->p_type == type) {
            return ph;
        }
    }
    return NULL;
}

struct elf64_shdr *
get_shdr(struct range prog, unsigned type, char *name) {
    struct range sheader = get_sheader(prog);
    struct range shnames = get_shnames(prog);
    struct elf64_ehdr *eh = get_ehdr(prog);

    for ( void *cur = sheader.beg; cur < sheader.end; cur += eh->e_shentsize) {
        struct elf64_shdr *es = cur;
        if (es->sh_type != type) {
            continue;
        }
        char *sh_name = shnames.beg + es->sh_name;
        xinbound(sh_name, shnames);

        if (strcmp(sh_name, name) == 0) {
            return es;
        }
    }
    return NULL;
}

struct rangearr
get_sharr(struct range prog, unsigned type, char *name) {
    struct rangearr a;

    struct elf64_shdr *sh = get_shdr(prog, type, name);
    xensurex(sh);
    a.beg = prog.beg + sh->sh_offset;
    a.end = a.beg + sh->sh_size;
    a.esz = sh->sh_entsize;
    xinrange(a, prog);

    return a;
}

struct rangearr
get_strtab(struct range prog) {
    return get_sharr(prog, SHT_STRTAB, ".strtab");
}

struct rangearr
get_symtab(struct range prog) {
    return get_sharr(prog, SHT_SYMTAB, ".symtab");
}

struct rangearr
get_dynamic(struct range prog) {
    return get_sharr(prog, SHT_DYNAMIC, ".dynamic");
}

struct elf64_sym *
get_sym(struct range prog, unsigned type, char *name) {
    struct rangearr symtab = get_symtab(prog);
    struct rangearr strtab = get_strtab(prog);

    for (void *cur = symtab.beg; cur < symtab.end; cur += symtab.esz) {
        struct elf64_sym *s = cur;
        if ((s->st_info & 0xf) != type  || s->st_name == 0) {
            continue;
        }
        char *sym_name = strtab.beg + s->st_name;
        xinbound(sym_name, strtab);
        if (strcmp(sym_name, name) == 0) {
            return s;
        }
    }
    return NULL;
}

void
list_funcs(struct range prog, struct arr *segments) {
    struct rangearr symtab = get_symtab(prog);
    struct rangearr strtab = get_strtab(prog);

    dbg("func: addr, size, off, name");
    for (void *cur = symtab.beg; cur < symtab.end; cur += symtab.esz) {
        struct elf64_sym *s = cur;
        if ((s->st_info & 0xf) != STT_FUNC) {
            continue;
        }
        if (s->st_name) {
            char *name = strtab.beg + s->st_name;
            xinbound(name, strtab);
            struct segment *seg = NULL;
            for (size_t i = 0; i < segments->size; i++) {
                struct segment *cur = arr_get(segments, i);
                if (s->st_value >= cur->mmbeg && s->st_value < cur->mmend) {
                    seg = cur;
                    break;
                }
            }
            if (!seg || s->st_size == 0) {
                continue;
            }
            size_t off = s->st_value - seg->mmbeg + seg->off;
            if (verbose) {
                printf("func: 0x%06lx, 0x%04lx, 0x%06lx, %s\n"
                    , s->st_value, s->st_size, off, name
                );
            } else {
                puts(name);
            }
        }
    }
}

void
instr_func(struct range prog, struct arr *segments, char *name
    , struct str **exec, uintptr_t exec_vpos, char *new_prog_beg
) {
    struct elf64_sym *f = get_sym(prog, STT_FUNC, name);

    if (f == NULL) {
        dbg("function not found: %s", name);
        return;
    }
    struct segment *s = NULL;
    for (size_t i = 0; i < segments->size; i++) {
        struct segment *cur = arr_get(segments, i);
        if (f->st_value >= cur->mmbeg && f->st_value < cur->mmend) {
            s = cur;
            break;
        }
    }
    assert(s != NULL);
    size_t off = f->st_value - s->mmbeg + s->off;
    dbg("elf: %s: addr: 0x%lx, size: 0x%lx, addr: 0x%lx", name
        , f->st_value, f->st_size, off
    );
    size_t virt_diff = f->st_value - off;

    csh h;
    if (cs_open(CS_ARCH_X86, CS_MODE_64, &h) != CS_ERR_OK) {
        errx(1, "cs_open");
    }
    cs_opt_skipdata skipdata = { .mnemonic = "db", };
    cs_option(h, CS_OPT_DETAIL, CS_OPT_ON);
    cs_option(h, CS_OPT_SKIPDATA, CS_OPT_ON);
    cs_option(h, CS_OPT_SKIPDATA_SETUP, (size_t)&skipdata);

    ks_engine *ks;
    xensure(ks_open(KS_ARCH_X86, KS_MODE_64, &ks) == 0); 
    ks_option(ks, KS_OPT_SYNTAX, KS_OPT_SYNTAX_INTEL);

    cs_insn *insn;
    size_t ni = cs_disasm(h, prog.beg + off, f->st_size, f->st_value, 0
        , &insn
    );
    struct arr *patch_jmp   __clean = arr_init(sizeof(struct jmpinfo), 0x100);
    struct arr *nopatch_jmp __clean = arr_init(sizeof(struct jmpinfo), 0x100);
    struct arr *offs        __clean = arr_init(sizeof(size_t), 0x100);
    struct arr *movable_seq __clean = arr_init(sizeof(struct range), 0x100);
    size_t curr_off = off;

    for (struct cs_insn *i = insn; i < insn + ni; i++) {
        xensure(arr_push(&offs, &curr_off) == 0);
        enum jmpkind jk = jmpclass(i->mnemonic);
        size_t off = curr_off;
        size_t ins_size = i->size ? i->size : 1;
        curr_off += ins_size;

        if (jk == INVALID_JMP) {
            dbg("asm: <%lx/%lx,%lx> %s %s", i->address, off, ins_size
                , i->mnemonic, i->op_str
            );
            continue;
        }
        char *end, *beg = i->op_str;
        u64 dest = strtoll(beg, &end, 16);
        if (end != beg + strlen(beg)) {
            dbg("cannot instrument %s, unpredictable jmp: <0x%lx> %s %s"
                , name, i->address, i->mnemonic, i->op_str
            );
            goto INSTR_END;
        }
        dbg("asm: <%lx/%lx,%lx> %s %s # %lx", i->address, off, ins_size
            , i->mnemonic, i->op_str, dest - virt_diff
        );
        struct jmpinfo ji = (struct jmpinfo) { .from = i->address
            , .into = dest
            , .len = i->size
            , .kind = jk
            , .insnum = i - insn
        };
        if (i->size < MOVSEQ_MAX) {
            xensure(arr_push(&nopatch_jmp, &ji) == 0);
        } else {
            xensure(arr_push(&patch_jmp, &ji) == 0);
        }
    }
    for (size_t i = 0; i < patch_jmp->size; i++) {
        struct jmpinfo *ji = arr_get(patch_jmp, i);
        dbg("jmp: patchable: <%lx> %s 0x%lx", ji->from, jmpstr[ji->kind]
            , ji->into
        );
    }
    for (size_t i = 0; i < nopatch_jmp->size; i++) {
        struct jmpinfo *ji = arr_get(nopatch_jmp, i);
        dbg("jmp: non patchable: <%lx> %s 0x%lx", ji->from
            , jmpstr[ji->kind], ji->into
        );
    }
    for (struct cs_insn *i = insn; i < insn + ni; i++) {
        if (strncmp(i->mnemonic, "nop", 3) == 0) continue;
        if (strncmp(i->mnemonic, "lea", 3) == 0) continue;
        if (strchr(i->op_str, '[') == NULL) continue;
        if (strstr(i->op_str, "rip") != NULL) continue;
        struct cs_insn *movable_seq_beg = i;
        struct cs_insn *movable_seq_cur = i;
        size_t seq_size = 0;
        int skip = 0;

        for (; movable_seq_cur < insn + ni; movable_seq_cur++) {
            if (strcmp(movable_seq_cur->mnemonic, "ret") == 0) {
                skip = 1;
                break;
            }
            if (strstr(i->op_str, "rip") != NULL) {
                skip = 1;
                break;
            }
            for (size_t i = 0; i < nopatch_jmp->size; i++) {
                struct jmpinfo *ji = arr_get(nopatch_jmp, i);

                if (movable_seq_cur->address == ji->from
                    || movable_seq_cur->address == ji->into
                ) {
                    skip = 1;
                    break;
                }
            }
            if (skip) break;
            if ((seq_size = seq_size + movable_seq_beg->size) >= MOVSEQ_MAX) {
                break;
            }
        }
        if (skip) continue;
        if (seq_size < MOVSEQ_MAX) break;

        i = movable_seq_cur;
        struct range seq = { .beg = movable_seq_beg, .end = movable_seq_cur + 1 };
        xensure(arr_push(&movable_seq, &seq) == 0);
    }
    for (size_t i = 0, j = 0; i < movable_seq->size; i++) {
        struct range *seq = arr_get(movable_seq, i);
        for (cs_insn *beg = seq->beg, *end = seq->end; beg != end; beg++, j++) {
            dbg("ins %.2ld/seq %.2ld: %s %s", j, i, beg->mnemonic, beg->op_str);
        }
    }
    char insstr[256], tmpins[256];

    struct str *movedistr __clean = str_init(0x100);
    struct arr *movedseqs __clean = arr_init(sizeof(struct movableseq), 0x100);
    xensure(movedistr);
    xensure(movedseqs);

    unsigned char *code = NULL;
    size_t nins, codesz = 0;

    for (size_t i = 0, j = 0; i < movable_seq->size; i++) {
        struct range *seq = arr_get(movable_seq, i);
        cs_insn *seq_beg = seq->beg;
        cs_insn *seq_end = seq->end;
        struct movableseq ms = { .len = seq_end - seq_beg, };
        assert(ms.len && ms.len <= MOVSEQ_MAX);

        for (int it = 0; it != ms.len; it++, j++) {
            movedistr->size = 0;
            cs_insn *ins = seq_beg + it;
            size_t code_vpos = exec_vpos + (*exec)->size;
            ms.seq[it].oldloc = ins->address;
            ms.seq[it].oldlen = ins->size;
            ms.seq[it].newloc = code_vpos;
            ms.seq[it].insnum = ins - insn;
            size_t *off = arr_get(offs, ins - insn);

            sprintf(insstr, "%s %s\n", ins->mnemonic, ins->op_str);

            char *beg = eat_until(insstr, '[');
            char *end = eat_until(beg, ']');
            int ismem = *beg == '[';
            int iswrt = *eat_until(end, ',') == ',';
            size_t expect_nins = 0;

            if (ismem) {
                xensurex(*beg == '[' && *end == ']');
                sprintf(tmpins, "pushf\npush rax\npush %d\n", iswrt);
                xensure(str_push(&movedistr, tmpins, strlen(tmpins)) == 0);
                size_t saddrsz = end - beg + 1;
                size_t s = strlcpy(tmpins, "lea rax, ", sizeof(tmpins));
                strnlcpy(tmpins + s, beg, saddrsz, sizeof(tmpins) - saddrsz);
                xensure(str_push(&movedistr, tmpins, strlen(tmpins)) == 0);

                sprintf(tmpins, "\ncall 0x%lx\n", exec_vpos);
                xensure(str_push(&movedistr, tmpins, strlen(tmpins)) == 0);

                sprintf(tmpins, "pop rax\npop rax\npopf\n");
                xensure(str_push(&movedistr, tmpins, strlen(tmpins)) == 0);
                expect_nins = 8;
                xensurex(ks_asm(ks, movedistr->data, code_vpos, &code, &codesz
                    , &nins) == 0 && nins == expect_nins
                );
                xensure(str_push(exec, code, codesz) == 0);
            }
            xensure(str_push(exec, prog.beg + *off, ins->size) == 0);
        }
        struct insmap *fst = ms.seq, *lst = ms.seq + ms.len - 1;
        sprintf(tmpins, "jmp 0x%lx\n", lst->oldloc + lst->oldlen);
        size_t code_vpos = exec_vpos + (*exec)->size;
        xensurex(ks_asm(ks, tmpins, code_vpos, &code, &codesz
            , &nins) == 0 && nins == 1
        );
        xensure(str_push(exec, code, codesz) == 0);

        size_t *insoff_beg = arr_get(offs, fst->insnum);
        size_t *insoff_end = arr_get(offs, lst->insnum);
        char *seg_beg = new_prog_beg + *insoff_beg;
        char *seg_end = new_prog_beg + *insoff_end + lst->oldlen;

        sprintf(tmpins, "jmp 0x%lx\n", ms.seq[0].newloc);
        xensurex(ks_asm(ks, tmpins, ms.seq[0].oldloc, &code, &codesz
            , &nins) == 0 && nins == 1
        );
        xensurex((uintptr_t)(seg_end - seg_beg) >= codesz);
        memset(seg_beg, NOP, seg_end - seg_beg);
        memcpy(seg_beg, code, codesz);

        xensure(arr_push(&movedseqs, &ms) == 0);
    }
    for (size_t i = 0; i < patch_jmp->size; i++) {
        struct jmpinfo *ji  = arr_get(patch_jmp, i);
        size_t jmp_from_new = ji->from;
        size_t jmp_into_new = ji->into;
        size_t *jmp_off     = arr_get(offs, ji->insnum);
        char *jmp_ins_beg   = new_prog_beg + *jmp_off;

        for (size_t j = 0; j < movedseqs->size; j++) {
            struct movableseq *ms = arr_get(movedseqs, j);
            for (int k = 0; k < ms->len; k++) {
                struct insmap *im = ms->seq + k;
                if (ji->from == im->oldloc) {
                    jmp_from_new = im->newloc;
                    jmp_ins_beg  = (*exec)->data + im->newloc - exec_vpos;
                } else if (ji->into == im->oldloc) {
                    jmp_into_new = im->newloc;
                }
            }
        }
        sprintf(tmpins, "%s 0x%lx", jmpstr[ji->kind], jmp_into_new);
        xensurex(ks_asm(ks, tmpins, jmp_from_new, &code, &codesz
            , &nins) == 0 && nins == 1
        );
        char *jmp_ins_end = jmp_ins_beg + ji->len;
        memset(jmp_ins_beg, NOP, jmp_ins_end - jmp_ins_beg);
        memcpy(jmp_ins_beg, code, codesz);
    }
INSTR_END:
    ks_free(code);
    ks_close(ks);
    cs_free(insn, ni);
    cs_close(&h);
}

struct range
get_saver(void) {
    extern char _binary_saver_bin_start;
    extern char _binary_saver_bin_end;

    return (struct range){ .beg = &_binary_saver_bin_start
        , .end = &_binary_saver_bin_end
    };
}

void
help(void) {
    warnx("ifname [funcname] [-v]"
        "\n\tifname<string>: the file to instrument"
        "\n\tfuncname<string>: the function to instrument "
            "(default: list all functions)"
        "\n\t-v: set verbose mode on (default: off)"
    );
}

int
main(int argc, char *argv[]) {
    int e;
    char *mm;
    size_t mmsz;

    if (argc - 1 < 1) {
        help();
        errx(1, "not enough arguments");
    } else if (argc - 1 > 3) {
        help();
        errx(1, "too many arguments");
    }
    char *fname = NULL, *func_name = NULL;

    for (char **beg = argv + 1; beg != argv + argc; beg++) {
        if (strcmp(*beg, "-v") == 0) {
            verbose = 1;
        } else if (fname == NULL) {
            fname = *beg;
        } else {
            func_name = *beg;
        }
    }
    if (fname == NULL) {
        help();
        errx(1, "must provide a file to instrument");
    }
    char *instr_fname = malloc(strlen(fname) + strlen(".instr") + 1);

    if (instr_fname == NULL) {
        err(1, "creating %s", instr_fname);
    }
    sprintf(instr_fname, "%s.instr", fname);

    if ((e = openf(fname, &mm, &mmsz)) != 0) {
        err(1, "openf %s", fname);
    }
    struct range prog = { .beg = mm, .end = mm + mmsz, }, nprog;
    struct elf64_ehdr *eh = get_ehdr(prog);
    struct range pheader = get_pheader(prog);
    uintptr_t base_addr = ~0ull;

    for (void *cur = pheader.beg; cur < pheader.end; cur += eh->e_phentsize) {
        struct elf64_phdr *ph = cur;
        if (ph->p_type != PT_LOAD) {
            continue;
        }
        if (ph->p_offset == 0) {
            if (base_addr != ~0ull) {
                errx(1, "double mapped ELF begin");
            }
            base_addr = ph->p_vaddr;
        }
    }
    if (base_addr == ~0ull) {
        errx(1, "unmapped ELF begin");
    }
    for (void *cur = pheader.beg; cur < pheader.end; cur += eh->e_phentsize) {
        struct elf64_phdr *ph = cur;
        if (ph->p_type != PT_LOAD) {
            continue;
        }
        if (ph->p_vaddr < base_addr) {
            errx(1, "unsorted ELF segments");
        }
    }
    uintptr_t nphpos = 0;

    struct arr *segments = arr_init(sizeof(struct segment), 16);
    xensure(segments != NULL);

    dbg("page: off, vaddr, fsz, msz, align -> [beg - end]");
    for (void *cur = pheader.beg; cur < pheader.end; cur += eh->e_phentsize) {
        struct elf64_phdr *ph = cur;
        if (ph->p_type != PT_LOAD) {
            continue;
        }
        uintptr_t segment_beg = align_down(ph->p_vaddr - base_addr
            , ph->p_align
        );
        uintptr_t segment_end = align_up(ph->p_vaddr - base_addr + ph->p_memsz
            , ph->p_align
        );
        struct segment s = { .off = ph->p_offset
            , .size = ph->p_filesz
            , .mmbeg = segment_beg + base_addr
            , .mmend = segment_end + base_addr
        };
        xensure(arr_push(&segments, &s) == 0);
        nphpos = max(nphpos, segment_end);
        dbg("page: 0x%lx, 0x%lx, 0x%lx, 0x%lx, 0x%lx -> [0x%lx - 0x%lx]"
            , ph->p_offset, ph->p_vaddr, ph->p_filesz, ph->p_memsz, ph->p_align
            , segment_beg + base_addr, segment_end + base_addr
        );
    }
    nphpos = align_up(nphpos, 0x1000);

    if (nphpos < mmsz) {
        // could be less wasteful and separate vaddr/offset
        nphpos = align_up(mmsz, 0x1000);
    }
    dbg("elf: nphpos: 0x%lx", nphpos);

    struct range saver = get_saver();
    struct str *exec = str_init(saver.end - saver.beg + 0x1000);
    xensure(str_push(&exec, saver.beg, saver.end - saver.beg) == 0);

    if (func_name == NULL) {
        list_funcs(prog, segments);
        return 0;
    }

    struct elf64_shdr *sh_rela = get_shdr(prog, SHT_RELA, ".rela.dyn");

    unsigned add_nsegments = 4;
    if (sh_rela != NULL) add_nsegments += 1;

    size_t datasz = 0x1000;
    uintptr_t nphsz = (eh->e_phnum + add_nsegments) * eh->e_phentsize;
    uintptr_t exec_off = align_up(nphpos + nphsz, 0x1000);
    uintptr_t data_vpos = exec_off;
    uintptr_t exec_vpos = data_vpos + datasz;

    size_t nmmsz = exec_off + exec->size;
    void *nmm = calloc(1, nmmsz);
    nprog = (struct range) { .beg = nmm, .end = nmm + nmmsz, };
    xensure(nmm != NULL);

    memcpy(nprog.beg, mm, mmsz);
    memcpy(nprog.beg + nphpos, pheader.beg, pheader.end - pheader.beg);

    instr_func(prog, segments, func_name, &exec, base_addr + exec_vpos, nprog.beg);
    nmmsz = exec_off + exec->size;
    xensure(range_resize(&nprog, nmmsz) == 0);
    memcpy(nprog.beg + exec_off, exec->data, exec->size);

    struct elf64_ehdr *neh = nprog.beg;
    neh->e_phoff = nphpos;
    neh->e_phnum = eh->e_phnum + add_nsegments;

    struct elf64_phdr *ph;
    ph = nprog.beg + nphpos + (eh->e_phnum + 0) * eh->e_phentsize;
    ph->p_type      = PT_LOAD;
    ph->p_flags     = PTF_READ;
    ph->p_offset    = nphpos;
    ph->p_vaddr     = base_addr + nphpos;
    ph->p_paddr     = base_addr + nphpos;
    ph->p_filesz    = nphsz;
    ph->p_memsz     = nphsz;
    ph->p_align     = 0x1000;
    assert(((ph->p_vaddr - ph->p_offset) % 0x1000) == 0);

    ph = nprog.beg + nphpos + (eh->e_phnum + 1) * eh->e_phentsize;
    ph->p_type      = PT_LOAD;
    ph->p_flags     = PTF_READ | PTF_WRITE;
    ph->p_offset    = 0;
    ph->p_vaddr     = align_up(base_addr + data_vpos, 0x1000);
    ph->p_paddr     = align_up(base_addr + data_vpos, 0x1000);
    ph->p_filesz    = 0;
    ph->p_memsz     = datasz;
    ph->p_align     = 0x1000;
    assert(((ph->p_vaddr - ph->p_offset) % 0x1000) == 0);

    ph = nprog.beg + nphpos + (eh->e_phnum + 2) * eh->e_phentsize;
    ph->p_type      = PT_LOAD;
    ph->p_flags     = PTF_READ | PTF_EXEC;
    ph->p_offset    = exec_off;
    ph->p_vaddr     = base_addr + exec_vpos;
    ph->p_paddr     = base_addr + exec_vpos;
    ph->p_filesz    = exec->size;
    ph->p_memsz     = exec->size;
    ph->p_align     = 0x1000;
    assert(((ph->p_vaddr - ph->p_offset) % 0x1000) == 0);

    size_t iniarr_vpos = align_up(exec_vpos + exec->size, 0x1000);
    size_t iniarr_off = align_up(exec_off + exec->size, 0x1000);

    struct arr *iniarr = arr_init(sizeof(size_t), 16);

    struct elf64_shdr *sh_init = get_shdr(nprog, SHT_INIT_ARRAY, ".init_array");
    struct elf64_shdr *sh_fini = get_shdr(nprog, SHT_FINI_ARRAY, ".fini_array");
    xensurex(sh_init && sh_fini);
    xensurex(sh_init->sh_entsize == sizeof(size_t));
    xensurex(sh_fini->sh_entsize == sizeof(size_t));
    size_t initsz = sh_init->sh_size, finisz = sh_fini->sh_size;

    for (void *cur = prog.beg + sh_init->sh_offset
        ; cur < prog.beg + sh_init->sh_offset + sh_init->sh_size
        ; cur += sizeof(size_t)
    ) {
        size_t *i = cur;
        dbg("init: 0x%lx", *i);
        xensure(arr_push(&iniarr, cur) == 0);
    }

    size_t init_fini_dist = iniarr->size * sizeof(size_t);
    size_t ninitsz = init_fini_dist;

    for (void *cur = prog.beg + sh_fini->sh_offset
        ; cur < prog.beg + sh_fini->sh_offset + sh_fini->sh_size
        ; cur += sizeof(size_t)
    ) {
        size_t *f = cur;
        dbg("fini: 0x%lx", *f);
        xensure(arr_push(&iniarr, cur) == 0);
    }

    void *dumper_off = (saver.end - sizeof(size_t));
    size_t dumper_size = *(size_t *)dumper_off;
    size_t dumper_off_in_saver = (dumper_off - saver.beg) - dumper_size;

    size_t fini_to_add_off = base_addr + exec_vpos + dumper_off_in_saver;
    dbg("fini: add: 0x%lx", fini_to_add_off);
    xensure(arr_push(&iniarr, &fini_to_add_off) == 0);

    size_t iniarr_size = iniarr->size * sizeof(size_t);
    nmmsz = iniarr_off + iniarr_size;
    xensure(range_resize(&nprog, nmmsz) == 0);

    sh_init = get_shdr(nprog, SHT_INIT_ARRAY, ".init_array");
    sh_fini = get_shdr(nprog, SHT_FINI_ARRAY, ".fini_array");

    size_t nfinisz = iniarr->size * sizeof(size_t) - init_fini_dist;
    memcpy(nprog.beg + iniarr_off, iniarr->data, ninitsz + nfinisz);

    size_t newinitaddr, newfiniaddr;
    size_t oldinitaddr = sh_init->sh_addr, oldfiniaddr = sh_fini->sh_addr;
    size_t oldinitsz   = sh_init->sh_size, oldfinisz   = sh_fini->sh_size;

    struct rangearr ndyns = get_dynamic(nprog);
    for (void *cur = ndyns.beg; cur < ndyns.end; cur += ndyns.esz) {
        struct elf64_dyn *d = cur;
        switch(d->d_tag) {
        case DT_INIT_ARRAY:
            newinitaddr = base_addr + iniarr_vpos;
            dbg("dyn: init: 0x%lx -> 0x%lx", d->d_ptr, newinitaddr);
            xensurex(d->d_ptr == sh_init->sh_addr);
            sh_init->sh_addr = d->d_ptr = newinitaddr;
            sh_init->sh_offset = iniarr_off;
            break;
        case DT_INIT_ARRAYSZ:
            dbg("dyn: initsz: 0x%lx -> 0x%lx", d->d_val, ninitsz);
            xensurex(d->d_val == initsz);
            sh_init->sh_size = d->d_val = ninitsz;
            break;
        case DT_FINI_ARRAY:
            newfiniaddr = base_addr + iniarr_vpos + init_fini_dist;
            dbg("dyn: fini: 0x%lx -> 0x%lx", d->d_ptr, newfiniaddr);
            xensurex(d->d_ptr == sh_fini->sh_addr);
            sh_fini->sh_addr = d->d_ptr = newfiniaddr;
            sh_fini->sh_offset = iniarr_off + init_fini_dist;
            break;
        case DT_FINI_ARRAYSZ:
            dbg("dyn: finisz: 0x%lx -> 0x%lx", d->d_val, nfinisz);
            xensurex(d->d_val == finisz);
            sh_fini->sh_size = d->d_val = nfinisz;
            break;
        }
    }

    ph = nprog.beg + nphpos + (eh->e_phnum + 3) * eh->e_phentsize;
    ph->p_type      = PT_LOAD;
    ph->p_flags     = PTF_READ | PTF_WRITE;
    ph->p_offset    = iniarr_off;
    ph->p_vaddr     = base_addr + iniarr_vpos;
    ph->p_paddr     = base_addr + iniarr_vpos;
    ph->p_filesz    = iniarr_size;
    ph->p_memsz     = iniarr_size;
    ph->p_align     = 0x1000;
    assert(((ph->p_vaddr - ph->p_offset) % 0x1000) == 0);

    if (sh_rela && !base_addr) {
        size_t rela_vpos = align_up(iniarr_vpos + iniarr_size, 0x1000);
        size_t rela_size = sh_rela->sh_size + sizeof(struct elf64_rela);
        size_t rela_off = align_up(iniarr_off + iniarr_size, 0x1000);

        nmmsz = rela_off + rela_size;
        xensure(range_resize(&nprog, nmmsz) == 0);
        sh_rela = get_shdr(nprog, SHT_RELA, ".rela.dyn");

        memcpy(nprog.beg + rela_off, nprog.beg + sh_rela->sh_offset
            , sh_rela->sh_size
        );

        for (void *cur = nprog.beg + rela_off
            ; cur < nprog.beg + rela_off + sh_rela->sh_size
            ; cur += sh_rela->sh_entsize
        ) {
            struct elf64_rela *r = cur;
            dbg("rela: %lx %lx %lx", r->r_offset, r->r_info, r->r_addend);

            if ((r->r_info & 0xff) == R_X86_64_RELATIVE) {
#if 0           // why do init, fini behave differently?
                if (r->r_offset >= oldinitaddr
                    && r->r_offset < oldinitaddr + oldinitsz
                    && ((r->r_offset - oldinitaddr) % sh_init->sh_entsize) == 0
                ) {
                    size_t noff = r->r_offset + newinitaddr - oldinitaddr;
                    dbg("rela: sym: %lx -> %lx", r->r_offset, noff);
                    r->r_offset = noff;
                }
#else           // unused vars, don't touch init
                (void)oldinitaddr; (void)oldinitsz;
#endif
                if (r->r_offset >= oldfiniaddr
                    && r->r_offset < oldfiniaddr + oldfinisz
                    && ((r->r_offset - oldfiniaddr) % sh_fini->sh_entsize) == 0
                ) {
                    size_t noff = r->r_offset + newfiniaddr - oldfiniaddr;
                    dbg("rela: sym: %lx -> %lx", r->r_offset, noff);
                    r->r_offset = noff;
                }
            }
        }
        xensurex(sh_rela->sh_entsize >= sizeof(struct elf64_rela));
        struct elf64_rela *nrela = nprog.beg + rela_off + sh_rela->sh_size;
        nrela->r_offset = sh_fini->sh_addr + oldfinisz;
        nrela->r_info   = R_X86_64_RELATIVE;
        nrela->r_addend = fini_to_add_off;

        ph = nprog.beg + nphpos + (eh->e_phnum + 4) * eh->e_phentsize;
        ph->p_type      = PT_LOAD;
        ph->p_flags     = PTF_READ | PTF_WRITE;
        ph->p_offset    = rela_off;
        ph->p_vaddr     = base_addr + rela_vpos;
        ph->p_paddr     = base_addr + rela_vpos;
        ph->p_filesz    = rela_size;
        ph->p_memsz     = rela_size;
        ph->p_align     = 0x1000;
        assert(((ph->p_vaddr - ph->p_offset) % 0x1000) == 0);

        ndyns = get_dynamic(nprog);
        for (void *cur = ndyns.beg; cur < ndyns.end; cur += ndyns.esz) {
            struct elf64_dyn *d = cur;
            size_t oldval = d->d_val, oldoff;

            switch(d->d_tag) {
            case DT_RELA:
                oldoff = sh_rela->sh_offset;
                sh_rela->sh_offset = rela_off;
                dbg("rela: off: 0x%lx -> 0x%lx", oldoff, sh_rela->sh_offset);
                xensurex(d->d_val == sh_rela->sh_addr);
                d->d_val = base_addr + rela_vpos;
                dbg("rela: vpos: 0x%lx -> 0x%lx", oldval, d->d_val);
                break;
            case DT_RELASZ:
                xensurex(sh_rela->sh_size == d->d_val);
                sh_rela->sh_size = d->d_val = rela_size;
                dbg("rela: size: 0x%lx -> 0x%lx", oldval, d->d_val);
                break;
            }
        }
    }
    ph = get_phdr(nprog, PT_PHDR);
    ph->p_vaddr = base_addr + neh->e_phoff;
    ph->p_paddr = base_addr + neh->e_phoff;

    FILE *nf = fopen(instr_fname, "w");
    if (nf == NULL) {
        err(1, "fopen %s", instr_fname);
    }
    fwrite(nprog.beg, 1, nmmsz, nf);

    return 0;
}

// LICENSE
// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.
//
// In jurisdictions that recognize copyright laws, the author or authors
// of this software dedicate any and all copyright interest in the
// software to the public domain. We make this dedication for the benefit
// of the public at large and to the detriment of our heirs and
// successors. We intend this dedication to be an overt act of
// relinquishment in perpetuity of all present and future rights to this
// software under copyright law.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
//
// For more information, please refer to <http://unlicense.org/>
