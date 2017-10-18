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
	printEXP b;
	print ")"
	);

val vx = BID 1;
val vy = BID 2;
val vz = BID 3;


val t1 = BLAM (BID 1);
val t2 = BLAM (BID 2);
val t3 = BAPP (BAPP (t1, t2), BID 2);
val t4 = BAPP (BLAM (BID 1), BID 1);
val t5 = BAPP (BAPP (BAPP ( BLAM (BID 1), BLAM (BID 2)),BID 2), (BAPP (BAPP ( BLAM (BID 1), BLAM (BID 2)),BID 2)));
val t6 = BLAM (BLAM (BLAM ( BAPP (BAPP (BID 3, BID 2), BAPP (BID 2, BID 1)))));
val t7 = BAPP (BAPP ( t6, t1), t1);
val t8 = BLAM (BAPP (BID 1,BAPP( BLAM ( BID 1), BID 1)));
val t9 = BAPP (t8, t3);
val omega = BAPP ( BLAM (BAPP(BID 1, BID 1)), BLAM (BAPP(BID 1, BID 1)));
 

end
