datatype BEXP = BAPP of BEXP * BEXP
       | BLAM of BEXP
       | BID of int;
	   

fun printBEXP (BID x) = print (Int.toString x)
  | printBEXP (BLAM x) = (
	print "(\206\187";
	printBEXP x;
	print ")"
	)
  | printBEXP (BAPP (a, b)) = (
	print "(";
	printBEXP a;
	print " ";
	printBEXP b;
	print ")"
	);