use ExtUtils::MakeMaker;
use Config;
$Verbose = 1;
my $optimize = '-O3';
my $cc = $Config{cc};
my $longsize = $Config{longsize};
my $ptrsize = $Config{ptrsize};
my $define = "-DSIZEOF_VOID_P=$ptrsize -DSIZEOF_LONG=$longsize";
my $dlext = $Config{dlext};
my $libs = "-L../blib/arch/auto/Cudd/util -lutil";

WriteMakefile(
    CC		=> $cc,
    NAME	=> 'Cudd::mtr',
    INC		=> '-I../include',
    dynamic_lib	=> ($dlext eq dll) ? {OTHERLDFLAGS => $libs} : {},
    DEFINE	=> $define,
    clean	=> {'FILES' => 'libmtr.a'},
    OBJECT	=> '$(O_FILES)',
    OPTIMIZE	=> $optimize
);

sub MY::postamble {
	'
all :: static

static ::       libmtr$(LIB_EXT)

libmtr$(LIB_EXT): $(O_FILES)
	$(AR) cr libmtr$(LIB_EXT) $(O_FILES)
	$(RANLIB) libmtr$(LIB_EXT)

	';
}
