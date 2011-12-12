let ocamlc_spec = Some [
  "-a",
  false,
  " Build a library";

  "-annot",
  false,
  " Save information in <filename>.annot";

  "-c",
  false,
  " Compile only (do not link)";

  "-cc",
  true,
  "<command>  Use <command> as the C compiler and linker";

  "-cclib",
  true,
  "<opt>  Pass option <opt> to the C linker";

  "-ccopt",
  true,
  "<opt>  Pass option <opt> to the C compiler and linker";

  "-config",
  false,
  " Print configuration values and exit";

  "-custom",
  false,
  " Link in custom mode";

  "-dllib",
  true,
  "<lib>  Use the dynamically-loaded library <lib>";

  "-dllpath",
  true,
  "<dir>  Add <dir> to the run-time search path for shared libraries";

  "-dtypes",
  false,
  " (deprecated) same as -annot";

  "-for-pack",
  true,
  "<ident>  Ignored (for compatibility with ocamlopt)";

  "-g",
  false,
  " Save debugging information";

  "-i",
  false,
  " Print inferred interface";

  "-I",
  true,
  "<dir>  Add <dir> to the list of include directories";

  "-impl",
  true,
  "<file>  Compile <file> as a .ml file";

  "-intf",
  true,
  "<file>  Compile <file> as a .mli file";

  "-intf-suffix",
  true,
  "<string>  Suffix for interface files (default: .mli)";

  "-intf_suffix",
  true,
  "<string>  (deprecated) same as -intf-suffix";

  "-labels",
  false,
  " Use commuting label mode";

  "-linkall",
  false,
  " Link all modules, even unused ones";

  "-make-runtime",
  false,
  " Build a runtime system with given C objects and libraries";

  "-make_runtime",
  false,
  " (deprecated) same as -make-runtime";

  "-modern",
  false,
  " (deprecated) same as -labels";

  "-no-app-funct",
  false,
  " Deactivate applicative functors";

  "-noassert",
  false,
  " Do not compile assertion checks";

  "-noautolink",
  false,
  " Do not automatically link C libraries specified in .cma files";

  "-nolabels",
  false,
  " Ignore non-optional labels in types";

  "-nostdlib",
  false,
  " Do not add default directory to the list of include directories";

  "-o",
  true,
  "<file>  Set output file name to <file>";

  "-output-obj",
  false,
  " Output a C object file instead of an executable";

  "-pack",
  false,
  " Package the given .cmo files into one .cmo";

  "-pp",
  true,
  "<command>  Pipe sources through preprocessor <command>";

  "-principal",
  false,
  " Check principality of type inference";

  "-rectypes",
  false,
  " Allow arbitrary recursive types";

  "-strict-sequence",
  false,
  " Left-hand part of a sequence must have type unit";

  "-thread",
  false,
  " Generate code that supports the system threads library";

  "-unsafe",
  false,
  " Do not compile bounds checking on array and string access";

  "-use-runtime",
  true,
  "<file>  Generate bytecode for the given runtime system";

  "-use_runtime",
  true,
  "<file>  (deprecated) same as -use-runtime";

  "-v",
  false,
  " Print compiler version and location of standard library and exit";

  "-version",
  false,
  " Print version and exit";

  "-vnum",
  false,
  " Print version number and exit";

  "-verbose",
  false,
  " Print calls to external commands";

  "-vmthread",
  false,
  " Generate code that supports the threads library with VM-level\n     scheduling";

  "-w",
  true,
  "<list>  Enable or disable warnings according to <list>:\n        +<spec>   enable warnings in <spec>\n        -<spec>   disable warnings in <spec>\n        @<spec>   enable warnings in <spec> and treat them as errors\n     <spec> can be:\n        <num>             a single warning number\n        <num1>..<num2>    a range of consecutive warning numbers\n        <letter>          a predefined set\n     default setting is \"+a-4-6-7-9-27..29\"";

  "-warn-error",
  true,
  "<list>  Enable or disable error status for warnings according\n     to <list>.  See option -w for the syntax of <list>.\n     Default setting is \"-a\"";

  "-warn-help",
  false,
  "  Show description of warning numbers";

  "-where",
  false,
  " Print location of standard library and exit";

  "-nopervasives",
  false,
  " (undocumented)";

  "-use-prims",
  true,
  "<file>  (undocumented)";

  "-dparsetree",
  false,
  " (undocumented)";

  "-drawlambda",
  false,
  " (undocumented)";

  "-dlambda",
  false,
  " (undocumented)";

  "-dinstr",
  false,
  " (undocumented)";

  "-",
  true,
  "<file>  Treat <file> as a file name (even if it starts with `-')";

];;

let ocamlcp_spec = Some [
  "-p",
  true,
  "[afilmt]  Profile constructs specified by argument (default fm):\n      a  Everything\n      f  Function calls and method calls\n      i  if ... then ... else\n      l  while and for loops\n      m  match ... with\n      t  try ... with";

  "-a",
  false,
  " Build a library";

  "-annot",
  false,
  " Save information in <filename>.annot";

  "-c",
  false,
  " Compile only (do not link)";

  "-cc",
  true,
  "<command>  Use <command> as the C compiler and linker";

  "-cclib",
  true,
  "<opt>  Pass option <opt> to the C linker";

  "-ccopt",
  true,
  "<opt>  Pass option <opt> to the C compiler and linker";

  "-config",
  false,
  " Print configuration values and exit";

  "-custom",
  false,
  " Link in custom mode";

  "-dllib",
  true,
  "<lib>  Use the dynamically-loaded library <lib>";

  "-dllpath",
  true,
  "<dir>  Add <dir> to the run-time search path for shared libraries";

  "-dtypes",
  false,
  " (deprecated) same as -annot";

  "-for-pack",
  true,
  "<ident>  Ignored (for compatibility with ocamlopt)";

  "-g",
  false,
  " Save debugging information";

  "-i",
  false,
  " Print inferred interface";

  "-I",
  true,
  "<dir>  Add <dir> to the list of include directories";

  "-impl",
  true,
  "<file>  Compile <file> as a .ml file";

  "-intf",
  true,
  "<file>  Compile <file> as a .mli file";

  "-intf-suffix",
  true,
  "<string>  Suffix for interface files (default: .mli)";

  "-intf_suffix",
  true,
  "<string>  (deprecated) same as -intf-suffix";

  "-labels",
  false,
  " Use commuting label mode";

  "-linkall",
  false,
  " Link all modules, even unused ones";

  "-make-runtime",
  false,
  " Build a runtime system with given C objects and libraries";

  "-make_runtime",
  false,
  " (deprecated) same as -make-runtime";

  "-modern",
  false,
  " (deprecated) same as -labels";

  "-no-app-funct",
  false,
  " Deactivate applicative functors";

  "-noassert",
  false,
  " Do not compile assertion checks";

  "-noautolink",
  false,
  " Do not automatically link C libraries specified in .cma files";

  "-nolabels",
  false,
  " Ignore non-optional labels in types";

  "-nostdlib",
  false,
  " Do not add default directory to the list of include directories";

  "-o",
  true,
  "<file>  Set output file name to <file>";

  "-output-obj",
  false,
  " Output a C object file instead of an executable";

  "-pack",
  false,
  " Package the given .cmo files into one .cmo";

  "-pp",
  true,
  "<command>  Pipe sources through preprocessor <command>";

  "-principal",
  false,
  " Check principality of type inference";

  "-rectypes",
  false,
  " Allow arbitrary recursive types";

  "-strict-sequence",
  false,
  " Left-hand part of a sequence must have type unit";

  "-thread",
  false,
  " Generate code that supports the system threads library";

  "-unsafe",
  false,
  " Do not compile bounds checking on array and string access";

  "-use-runtime",
  true,
  "<file>  Generate bytecode for the given runtime system";

  "-use_runtime",
  true,
  "<file>  (deprecated) same as -use-runtime";

  "-v",
  false,
  " Print compiler version and location of standard library and exit";

  "-version",
  false,
  " Print version and exit";

  "-vnum",
  false,
  " Print version number and exit";

  "-verbose",
  false,
  " Print calls to external commands";

  "-vmthread",
  false,
  " Generate code that supports the threads library with VM-level\n     scheduling";

  "-w",
  true,
  "<list>  Enable or disable warnings according to <list>:\n        +<spec>   enable warnings in <spec>\n        -<spec>   disable warnings in <spec>\n        @<spec>   enable warnings in <spec> and treat them as errors\n     <spec> can be:\n        <num>             a single warning number\n        <num1>..<num2>    a range of consecutive warning numbers\n        <letter>          a predefined set\n     default setting is \"+a-4-6-7-9-27..29\"";

  "-warn-error",
  true,
  "<list>  Enable or disable error status for warnings according\n     to <list>.  See option -w for the syntax of <list>.\n     Default setting is \"-a\"";

  "-warn-help",
  false,
  "  Show description of warning numbers";

  "-where",
  false,
  " Print location of standard library and exit";

  "-nopervasives",
  false,
  " (undocumented)";

  "-use-prims",
  true,
  "<file>  (undocumented)";

  "-dparsetree",
  false,
  " (undocumented)";

  "-drawlambda",
  false,
  " (undocumented)";

  "-dlambda",
  false,
  " (undocumented)";

  "-dinstr",
  false,
  " (undocumented)";

  "-",
  true,
  "<file>  Treat <file> as a file name (even if it starts with `-')";

];;

let ocamlmktop_spec = Some [
  "-a",
  false,
  " Build a library";

  "-annot",
  false,
  " Save information in <filename>.annot";

  "-c",
  false,
  " Compile only (do not link)";

  "-cc",
  true,
  "<command>  Use <command> as the C compiler and linker";

  "-cclib",
  true,
  "<opt>  Pass option <opt> to the C linker";

  "-ccopt",
  true,
  "<opt>  Pass option <opt> to the C compiler and linker";

  "-config",
  false,
  " Print configuration values and exit";

  "-custom",
  false,
  " Link in custom mode";

  "-dllib",
  true,
  "<lib>  Use the dynamically-loaded library <lib>";

  "-dllpath",
  true,
  "<dir>  Add <dir> to the run-time search path for shared libraries";

  "-dtypes",
  false,
  " (deprecated) same as -annot";

  "-for-pack",
  true,
  "<ident>  Ignored (for compatibility with ocamlopt)";

  "-g",
  false,
  " Save debugging information";

  "-i",
  false,
  " Print inferred interface";

  "-I",
  true,
  "<dir>  Add <dir> to the list of include directories";

  "-impl",
  true,
  "<file>  Compile <file> as a .ml file";

  "-intf",
  true,
  "<file>  Compile <file> as a .mli file";

  "-intf-suffix",
  true,
  "<string>  Suffix for interface files (default: .mli)";

  "-intf_suffix",
  true,
  "<string>  (deprecated) same as -intf-suffix";

  "-labels",
  false,
  " Use commuting label mode";

  "-linkall",
  false,
  " Link all modules, even unused ones";

  "-make-runtime",
  false,
  " Build a runtime system with given C objects and libraries";

  "-make_runtime",
  false,
  " (deprecated) same as -make-runtime";

  "-modern",
  false,
  " (deprecated) same as -labels";

  "-no-app-funct",
  false,
  " Deactivate applicative functors";

  "-noassert",
  false,
  " Do not compile assertion checks";

  "-noautolink",
  false,
  " Do not automatically link C libraries specified in .cma files";

  "-nolabels",
  false,
  " Ignore non-optional labels in types";

  "-nostdlib",
  false,
  " Do not add default directory to the list of include directories";

  "-o",
  true,
  "<file>  Set output file name to <file>";

  "-output-obj",
  false,
  " Output a C object file instead of an executable";

  "-pack",
  false,
  " Package the given .cmo files into one .cmo";

  "-pp",
  true,
  "<command>  Pipe sources through preprocessor <command>";

  "-principal",
  false,
  " Check principality of type inference";

  "-rectypes",
  false,
  " Allow arbitrary recursive types";

  "-strict-sequence",
  false,
  " Left-hand part of a sequence must have type unit";

  "-thread",
  false,
  " Generate code that supports the system threads library";

  "-unsafe",
  false,
  " Do not compile bounds checking on array and string access";

  "-use-runtime",
  true,
  "<file>  Generate bytecode for the given runtime system";

  "-use_runtime",
  true,
  "<file>  (deprecated) same as -use-runtime";

  "-v",
  false,
  " Print compiler version and location of standard library and exit";

  "-version",
  false,
  " Print version and exit";

  "-vnum",
  false,
  " Print version number and exit";

  "-verbose",
  false,
  " Print calls to external commands";

  "-vmthread",
  false,
  " Generate code that supports the threads library with VM-level\n     scheduling";

  "-w",
  true,
  "<list>  Enable or disable warnings according to <list>:\n        +<spec>   enable warnings in <spec>\n        -<spec>   disable warnings in <spec>\n        @<spec>   enable warnings in <spec> and treat them as errors\n     <spec> can be:\n        <num>             a single warning number\n        <num1>..<num2>    a range of consecutive warning numbers\n        <letter>          a predefined set\n     default setting is \"+a-4-6-7-9-27..29\"";

  "-warn-error",
  true,
  "<list>  Enable or disable error status for warnings according\n     to <list>.  See option -w for the syntax of <list>.\n     Default setting is \"-a\"";

  "-warn-help",
  false,
  "  Show description of warning numbers";

  "-where",
  false,
  " Print location of standard library and exit";

  "-nopervasives",
  false,
  " (undocumented)";

  "-use-prims",
  true,
  "<file>  (undocumented)";

  "-dparsetree",
  false,
  " (undocumented)";

  "-drawlambda",
  false,
  " (undocumented)";

  "-dlambda",
  false,
  " (undocumented)";

  "-dinstr",
  false,
  " (undocumented)";

  "-",
  true,
  "<file>  Treat <file> as a file name (even if it starts with `-')";

];;

let ocamlopt_spec = Some [
  "-ffast-math",
  false,
  " Inline trigonometric and exponential functions";

  "-a",
  false,
  " Build a library";

  "-annot",
  false,
  " Save information in <filename>.annot";

  "-c",
  false,
  " Compile only (do not link)";

  "-cc",
  true,
  "<command>  Use <command> as the C compiler and linker";

  "-cclib",
  true,
  "<opt>  Pass option <opt> to the C linker";

  "-ccopt",
  true,
  "<opt>  Pass option <opt> to the C compiler and linker";

  "-compact",
  false,
  " Optimize code size rather than speed";

  "-config",
  false,
  " Print configuration values and exit";

  "-dtypes",
  false,
  " (deprecated) same as -annot";

  "-for-pack",
  true,
  "<ident>  Generate code that can later be `packed' with\n     ocamlopt -pack -o <ident>.cmx";

  "-g",
  false,
  " Record debugging information for exception backtrace";

  "-i",
  false,
  " Print inferred interface";

  "-I",
  true,
  "<dir>  Add <dir> to the list of include directories";

  "-impl",
  true,
  "<file>  Compile <file> as a .ml file";

  "-inline",
  true,
  "<n>  Set aggressiveness of inlining to <n>";

  "-intf",
  true,
  "<file>  Compile <file> as a .mli file";

  "-intf-suffix",
  true,
  "<string>  Suffix for interface files (default: .mli)";

  "-labels",
  false,
  " Use commuting label mode";

  "-linkall",
  false,
  " Link all modules, even unused ones";

  "-no-app-funct",
  false,
  " Deactivate applicative functors";

  "-noassert",
  false,
  " Do not compile assertion checks";

  "-noautolink",
  false,
  " Do not automatically link C libraries specified in .cmxa files";

  "-nodynlink",
  false,
  " Enable optimizations for code that will not be dynlinked";

  "-nolabels",
  false,
  " Ignore non-optional labels in types";

  "-nostdlib",
  false,
  " Do not add default directory to the list of include directories";

  "-o",
  true,
  "<file>  Set output file name to <file>";

  "-output-obj",
  false,
  " Output a C object file instead of an executable";

  "-p",
  false,
  " Compile and link with profiling support for \"gprof\"\n     (not supported on all platforms)";

  "-pack",
  false,
  " Package the given .cmx files into one .cmx";

  "-pp",
  true,
  "<command>  Pipe sources through preprocessor <command>";

  "-principal",
  false,
  " Check principality of type inference";

  "-rectypes",
  false,
  " Allow arbitrary recursive types";

  "-S",
  false,
  " Keep intermediate assembly file";

  "-strict-sequence",
  false,
  " Left-hand part of a sequence must have type unit";

  "-shared",
  false,
  " Produce a dynlinkable plugin";

  "-thread",
  false,
  " Generate code that supports the system threads library";

  "-unsafe",
  false,
  " Do not compile bounds checking on array and string access";

  "-v",
  false,
  " Print compiler version and location of standard library and exit";

  "-version",
  false,
  " Print version and exit";

  "-vnum",
  false,
  " Print version number and exit";

  "-verbose",
  false,
  " Print calls to external commands";

  "-w",
  true,
  "<list>  Enable or disable warnings according to <list>:\n        +<spec>   enable warnings in <spec>\n        -<spec>   disable warnings in <spec>\n        @<spec>   enable warnings in <spec> and treat them as errors\n     <spec> can be:\n        <num>             a single warning number\n        <num1>..<num2>    a range of consecutive warning numbers\n        <letter>          a predefined set\n     default setting is \"+a-4-6-7-9-27..29\"";

  "-warn-error",
  true,
  "<list>  Enable or disable error status for warnings according\n     to <list>.  See option -w for the syntax of <list>.\n     Default setting is \"-a\"";

  "-warn-help",
  false,
  "  Show description of warning numbers";

  "-where",
  false,
  " Print location of standard library and exit";

  "-nopervasives",
  false,
  " (undocumented)";

  "-dparsetree",
  false,
  " (undocumented)";

  "-drawlambda",
  false,
  " (undocumented)";

  "-dlambda",
  false,
  " (undocumented)";

  "-dcmm",
  false,
  " (undocumented)";

  "-dsel",
  false,
  " (undocumented)";

  "-dcombine",
  false,
  " (undocumented)";

  "-dlive",
  false,
  " (undocumented)";

  "-dspill",
  false,
  " (undocumented)";

  "-dinterf",
  false,
  " (undocumented)";

  "-dprefer",
  false,
  " (undocumented)";

  "-dalloc",
  false,
  " (undocumented)";

  "-dreload",
  false,
  " (undocumented)";

  "-dscheduling",
  false,
  " (undocumented)";

  "-dlinear",
  false,
  " (undocumented)";

  "-dstartup",
  false,
  " (undocumented)";

  "-",
  true,
  "<file>  Treat <file> as a file name (even if it starts with `-')";

];;

let ocamldep_spec = Some [
  "-I",
  true,
  "<dir>  Add <dir> to the list of include directories";

  "-impl",
  true,
  "<f> Process <f> as a .ml file";

  "-intf",
  true,
  "<f> Process <f> as a .mli file";

  "-ml-synonym",
  true,
  "<e> Consider <e> as a synonym of the .ml extension";

  "-mli-synonym",
  true,
  "<e> Consider <e> as a synonym of the .mli extension";

  "-modules",
  false,
  " Print module dependencies in raw form (not suitable for make)";

  "-native",
  false,
  "  Generate dependencies for a pure native-code project (no .cmo files)";

  "-pp",
  true,
  "<cmd> Pipe sources through preprocessor <cmd>";

  "-slash",
  false,
  "   (Windows) Use forward slash / instead of backslash \\ in file paths";

  "-version",
  false,
  " Print version and exit";

  "-vnum",
  false,
  " Print version number and exit";

];;

let ocamldoc_spec = Some [
  "-version",
  false,
  "\tPrint version and exit";

  "-vnum",
  false,
  "\tPrint version and exit";

  "-v",
  false,
  "\t\tverbose mode";

  "-I",
  true,
  "<dir>\tAdd <dir> to the list of include directories";

  "-pp",
  true,
  "<command>\tPipe sources through preprocessor <command>";

  "-impl",
  true,
  "<file>\tConsider <file> as a .ml file";

  "-intf",
  true,
  "<file>\tConsider <file> as a .mli file";

  "-text",
  true,
  "<file>\tConsider <file> as a .txt file";

  "-rectypes",
  false,
  "\tAllow arbitrary recursive types";

  "-nolabels",
  false,
  "\tIgnore non-optional labels in types";

  "-warn-error",
  false,
  "\tTreat ocamldoc warnings as errors";

  "-hide-warnings",
  false,
  "\n\t\tdo not print ocamldoc warnings";

  "-o",
  true,
  "<file>\tSet the output file name, used by texi, latex and dot generators\n\t\t(default is ocamldoc.out)\n\t\tor the prefix of index files for the HTML generator\n\t\t(default is index)";

  "-d",
  true,
  "<dir>\tGenerate files in directory <dir>, rather than in current\n\t\tdirectory (for man and HTML generators)";

  "-sort",
  false,
  "\tSort the list of top modules before generating the documentation";

  "-no-stop",
  false,
  "\tDo not stop at (**/**) comments";

  "-no-custom-tags",
  false,
  "\n\t\tDo not allow custom @-tags";

  "-stars",
  false,
  "\tRemove beginning blanks of comment lines, until the first '*'";

  "-inv-merge-ml-mli",
  false,
  "\n\t\tInverse implementations and interfaces when merging";

  "-no-module-constraint-filter",
  false,
  "\n\t\tDo not filter module elements using module type constraints";

  "-keep-code",
  false,
  "\tAlways keep code when available\n";

  "-dump",
  true,
  "<file>\tDump collected information into <file>";

  "-load",
  true,
  "<file>\tLoad information from <file> ; may be used several times\n";

  "-t",
  true,
  "<title>\tUse <title> as title for the generated documentation";

  "-intro",
  true,
  "<file>\tUse content of <file> as ocamldoc text to use as introduction\n\t\t(HTML, LaTeX and TeXinfo only)";

  "-hide",
  true,
  "<M1,M2.M3,...>\n\t\tHide the given complete module names in generated doc";

  "-m",
  true,
  "<options>\tspecify merge options between .mli and .ml\n\t\t<options> can be one or more of the following characters:\n\t\td  merge description\n\t\ta  merge @author\n\t\tv  merge @version\n\t\tl  merge @see\n\t\ts  merge @since\n\t\tb  merge @before\n\t\to  merge @deprecated\n\t\tp  merge @param\n\t\te  merge @raise\n\t\tr  merge @return\n\t\tc  merge custom @-tags\n\t\tA  merge all\n\n *** choosing a generator ***\n";

  "-html",
  false,
  "\tGenerate HTML documentation";

  "-latex",
  false,
  "\tGenerate LaTeX documentation";

  "-texi",
  false,
  "\tGenerate TeXinfo documentation";

  "-man",
  false,
  "\t\tGenerate man pages";

  "-dot",
  false,
  "\t\tGenerate dot code of top modules dependencies";

  "-customdir",
  false,
  "\tDisplay custom generators standard directory and exit";

  "-i",
  true,
  "<dir>\tAdd the given directory to the search path for custom\n\t\tgenerators";

  "-g",
  true,
  "<file.cm[o|a|xs]>\n\t\tLoad file defining a new documentation generator\n\n *** HTML options ***\n";

  "-all-params",
  false,
  "\tDisplay the complete list of parameters for functions and\n\t\tmethods (HTML only)";

  "-css-style",
  true,
  "<file>\n\t\tUse content of <file> as CSS style definition (HTML only)";

  "-index-only",
  false,
  "\tGenerate index files only (HTML only)";

  "-colorize-code",
  false,
  "\n\t\tColorize code even in documentation pages (HTML only)";

  "-short-functors",
  false,
  "\n\t\tUse short form to display functor types (HTML only)";

  "-charset",
  true,
  "<s>\n\t\tAdd information about character encoding being s\n\t\t(default is iso-8859-1)\n\n *** LaTeX options ***\n";

  "-noheader",
  false,
  "\tSuppress header in generated documentation\n\t\t(LaTeX and TeXinfo only)";

  "-notrailer",
  false,
  "\tSuppress trailer in generated documentation\n\t\t(LaTeX and TeXinfo only)";

  "-sepfiles",
  false,
  "\tGenerate one file per toplevel module (LaTeX only)";

  "-latextitle",
  false,
  "n,style\n\t\tAssociate {n } to the given sectionning style\n\t\t(e.g. 'section') in the latex output (LaTeX only)\n\t\tDefault sectionning is:\n\t\t 1 -> section\n\t\t 2 -> subsection\n\t\t 3 -> subsubsection\n\t\t 4 -> paragraph\n\t\t 5 -> subparagraph";

  "-latex-value-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of values.\n\t\t(default is \"val:\")";

  "-latex-type-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of types.\n\t\t(default is \"type:\")";

  "-latex-exception-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of exceptions.\n\t\t(default is \"exception:\")";

  "-latex-attribute-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of attributes.\n\t\t(default is \"val:\")";

  "-latex-method-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of methods.\n\t\t(default is \"method:\")";

  "-latex-module-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of modules.\n\t\t(default is \"module:\")";

  "-latex-module-type-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of module types.\n\t\t(default is \"moduletype:\")";

  "-latex-class-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of classes.\n\t\t(default is \"class:\")";

  "-latex-class-type-prefix",
  true,
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of class types.\n\t\t(default is \"classtype:\")";

  "-notoc",
  false,
  "\tDo not generate table of contents (LaTeX only)\n\n *** texinfo options ***\n";

  "-noindex",
  false,
  "\tDo not build index for Info files (TeXinfo only)";

  "-esc8",
  false,
  "\tEscape accentuated characters in Info files (TeXinfo only)";

  "-info-section",
  false,
  "Specify section of Info directory (TeXinfo only)";

  "-info-entry",
  false,
  "\tSpecify Info directory entry (TeXinfo only)\n\n *** dot options ***\n";

  "-dot-colors",
  true,
  "<c1,c2,...,cn>\n\t\tUse colors c1,c1,...,cn in the dot output\n\t\t(default list is darkturquoise,darkgoldenrod2,cyan,green,\n\t\tmagenta,yellow,burlywood1,aquamarine,floralwhite,lightpink,\n\t\tlightblue,mediumturquoise,salmon,slategray3)";

  "-dot-include-all",
  false,
  "\n\t\tInclude all modules in the dot output, not only the\n\t\tmodules given on the command line";

  "-dot-types",
  false,
  "\tGenerate dependency graph for types instead of modules";

  "-dot-reduce",
  false,
  "\tPerform a transitive reduction on the selected dependency graph\n\t\tbefore the dot output\n\n *** man pages options ***\n";

  "-man-mini",
  false,
  "\tGenerate man pages only for modules, module types, classes\n\t\tand class types (man only)";

  "-man-suffix",
  true,
  "<suffix>\n\t\tUse <suffix> for man page files (default is 3o) (man only)\n";

  "-man-section",
  true,
  "<section>\n\t\tUse <section> in man page files (default is 3) (man only)\n";

];;

