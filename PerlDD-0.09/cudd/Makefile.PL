use ExtUtils::MakeMaker;
use Config;
$Verbose = 1;
my $optimize = '-O3';
my $cc = $Config{cc};
my $longsize = $Config{longsize};
my $ptrsize = $Config{ptrsize};
my $define = "-DHAVE_IEEE_754 -DSIZEOF_VOID_P=$ptrsize -DSIZEOF_LONG=$longsize";my $dlext = $Config{dlext};
my $libs = "-L../blib/arch/auto/Cudd/util -lutil -L../blib/arch/auto/Cudd/epd -lepd -L../blib/arch/auto/Cudd/mtr -lmtr -L../blib/arch/auto/Cudd/st -lst";

WriteMakefile(
    CC		=> $cc,
    NAME	=> 'Cudd::cudd',
    INC		=> '-I../include',
    dynamic_lib => ($dlext eq dll) ? {OTHERLDFLAGS => $libs} : {},
    DEFINE	=> $define,
    clean	=> {'FILES' => 'libcudd.a'},
    OBJECT	=> '$(O_FILES)',
    OPTIMIZE	=> $optimize
);

sub MY::postamble {
	'
all :: static

static ::       libcudd$(LIB_EXT)

libcudd$(LIB_EXT): $(O_FILES)
	$(AR) cr libcudd$(LIB_EXT) $(O_FILES)
	$(RANLIB) libcudd$(LIB_EXT)

	';
}
