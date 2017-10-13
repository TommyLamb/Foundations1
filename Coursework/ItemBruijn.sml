datatype IBEXP = IBAPP of IBEXP * IBEXP
       | IBLAM of IBEXP
       | IBID of int;
	   

fun printIBEXP (IBID x) = print (Int.toString x)
  | printIBEXP (IBLAM x) = (
	print "[]";
	printIBEXP x
	)
  | printIBEXP (IBAPP (a, b)) = (
	print "<";
	printIBEXP a;
	print ">";
	printIBEXP b
	);