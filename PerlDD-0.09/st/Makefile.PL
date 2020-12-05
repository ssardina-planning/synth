use ExtUtils::MakeMaker;
use Config;
$Verbose = 1;
my $optimize = '-O3';
my $cc = $Config{cc};
my $dlext = $Config{dlext};
my $libs = "-L../blib/arch/auto/Cudd/util -lutil";

WriteMakefile(
    CC		=> $cc,
    NAME	=> 'Cudd::st',
    INC		=> '-I../include',
    dynamic_lib => ($dlext eq dll) ? {OTHERLDFLAGS => $libs} : {},
    clean	=> {'FILES' => 'libst.a'},
    OBJECT	=> '$(O_FILES)',
    OPTIMIZE	=> $optimize
);

sub MY::postamble {
	'
all :: static

static ::       libst$(LIB_EXT)

libst$(LIB_EXT): $(O_FILES)
	$(AR) cr libst$(LIB_EXT) $(O_FILES)
	$(RANLIB) libst$(LIB_EXT)

	';
}
