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

val vx = IBID 1;
val vy = IBID 2;
val vz = IBID 3;
	
val t1 = IBLAM (IBID 1);
val t2 = IBLAM (IBID 2);
val t3 = IBAPP (IBAPP (t2, t1), IBID 2);
val t4 = IBAPP (IBID 1, IBLAM (IBID 1));
val t5 = IBAPP ((IBAPP (IBID 2,IBAPP (IBLAM (IBID 2), IBLAM (IBID 1)))),IBAPP (IBID 2, IBAPP (IBLAM (IBID 2), IBLAM (IBID 1))));
val t6 = IBLAM (IBLAM (IBLAM ( IBAPP (IBAPP (IBID 1, IBID 2), IBAPP (IBID 2, IBID 3)))));
val t7 = IBAPP (t1, IBAPP ( t1, t6));
val t8 = IBLAM (IBAPP (IBAPP(IBID 1, IBLAM ( IBID 1)), IBID 1));
val t9 = IBAPP (t3, t8);
val omega = IBAPP ( IBLAM (IBAPP(IBID 1, IBID 1)), IBLAM (IBAPP(IBID 1, IBID 1)));
 
end
