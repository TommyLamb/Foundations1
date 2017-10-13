datatype IEXP = IAPP of IEXP * IEXP
       | ILAM of string * IEXP
       | IID of string;
	   

fun printIEXP (IID x) = print x
  | printIEXP (ILAM (x, y)) = (
	print "[";
	print x;
	print "]";
	printIEXP y
	)
  | printIEXP (IAPP (a, b)) = (
	print "<";
	printIEXP a;
	print ">";
	printIEXP b
	);