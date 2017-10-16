structure Bruijn = struct

fun printEXP (BID x) = print (Int.toString x)
  | printEXP (BLAM x) = (
	print "(\206\187";
	printEXP x;
	print ")"
	)
  | printEXP (BAPP (a, b)) = (
	print "(";
	printEXP a;
	print " ";
	printEXP b;
	print ")"
	);

end
