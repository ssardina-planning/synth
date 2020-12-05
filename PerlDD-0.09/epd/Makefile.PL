use ExtUtils::MakeMaker;
use Config;
$Verbose = 1;
my $optimize = '-O3';
my $cc = $Config{cc};
my $dlext = $Config{dlext};
my $libs = "-L../blib/arch/auto/Cudd/util -lutil";

WriteMakefile(
    CC		=> $cc,
    NAME	=> 'Cudd::epd',
    INC		=> '-I../include',
    dynamic_lib => ($dlext eq dll) ? {OTHERLDFLAGS => $libs} : {},
    clean	=> {'FILES' => 'libepd.a'},
    OBJECT	=> '$(O_FILES)',
    OPTIMIZE	=> $optimize
);

sub MY::postamble {
	'
all :: static

static ::       libepd$(LIB_EXT)

libepd$(LIB_EXT): $(O_FILES)
	$(AR) cr libepd$(LIB_EXT) $(O_FILES)
	$(RANLIB) libepd$(LIB_EXT)

	';
}
