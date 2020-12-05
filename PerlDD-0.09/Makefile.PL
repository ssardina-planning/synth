use ExtUtils::MakeMaker;
use Config;
my $define = '';
# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.
WriteMakefile(
    'NAME'	   => 'Cudd',
    'DISTNAME'     => 'PerlDD',
    'VERSION_FROM' => 'Cudd.pm', # finds $VERSION
    'AUTHOR'       => 'Fabio Somenzi',
    'DIR'          => ['util', 'mtr', 'st', 'epd', 'cudd'],
    'DEFINE'	   => $define,
    'OPTIMIZE'     => '-O3',
    'INC'	   => '-I./include',
    'MYEXTLIB'     => 'cudd/libcudd$(LIB_EXT) mtr/libmtr$(LIB_EXT) st/libst$(LIB_EXT) epd/libepd$(LIB_EXT) util/libutil$(LIB_EXT)',
    'LIBS'         => ['-lm'],
    'OBJECT'       => '$(O_FILES)',
    'dist'         => {COMPRESS => 'gzip -9', SUFFIX => 'gz',},
);

sub MY::postamble {
'
$(MYEXTLIB): cudd/Makefile mtr/Makefile st/Makefile epd/Makefile util/Makefile
	cd util && $(MAKE)
	cd mtr && $(MAKE)
	cd st && $(MAKE)
	cd epd && $(MAKE)
	cd cudd && $(MAKE)
';
}
