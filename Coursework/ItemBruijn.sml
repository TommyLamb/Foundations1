structure ItemBruijn = struct

fun printEXP (IBID x) = print (Int.toString x)
  | printEXP (IBLAM x) = (
	print "[]";
	printEXP x
	)
  | printEXP (IBAPP (a, b)) = (
	print "<";
	printEXP a;
	print ">";
	printEXP b
	);

end
