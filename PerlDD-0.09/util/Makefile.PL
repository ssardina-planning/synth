use ExtUtils::MakeMaker;
use Config;
$Verbose = 1;
my $cc = $Config{cc};
my $define = '';
if ($Config{d_sysconf} eq 'define') {
    $define = '-DHAVE_SYSCONF';
}
if ($Config{i_systypes} eq 'define') {
    $define .= ' -DHAVE_SYS_TYPES_H';
}
if ($Config{i_systimes} eq 'define') {
    $define .= ' -DHAVE_SYS_TIMES_H';
}

WriteMakefile(
    'CC'	=> $cc,
    'NAME'	=> 'Cudd::util',
    'INC'	=> '',
    'DEFINE'	=> $define,
    'clean'	=> {'FILES' => 'libutil.a'},
    'OBJECT'	=> '$(O_FILES)',
    'OPTIMIZE'	=> '-O3'
);

sub MY::postamble {
	'
all :: static

static ::       libutil$(LIB_EXT)

libutil$(LIB_EXT): $(O_FILES)
	$(AR) cr libutil$(LIB_EXT) $(O_FILES)
	$(RANLIB) libutil$(LIB_EXT)

	';
}
