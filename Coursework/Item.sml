structure Item = struct


(* Note that the ordering here is due to the inability to equality test during patern matching, 
*  f (x, x) is erronous in SML. Also due to the fact that any if statement must have an else clause. 
*  Also becuase ( CID x, CID y) and (CID x, COM y) are not mutually exclusive *)
fun f (CID x, CAPP (a, b)) = 
	if (((CID x) = b) andalso (not (Combinatorics.free (CID x) a))) then
		a
	else
		CAPP( CAPP (CS, f ((CID x), a)), f ((CID x), b))
  | f (CID x, a) =
	if ((CID x) = a) then (* Clause 1 *)
		CI 
	else (* clause 2 *)
		 CAPP (CK, a); (* See comment on supporting documentation for omission of conditional *)

fun toCombinatorics (IID x) = CID x
  | toCombinatorics (IAPP (a, b)) = CAPP (toCombinatorics b, toCombinatorics a)
  | toCombinatorics (ILAM (x, a)) = f (CID x, (toCombinatorics a));

fun printEXP (IID x) = print x
  | printEXP (ILAM (x, y)) = (
	print "[";
	print x;
	print "]";
	printEXP y
	)
  | printEXP (IAPP (a, b)) = (
	print "<";
	printEXP a;
	print ">";
	printEXP b
	);

val vx = IID "x";
val vy = IID "y";
val vz = IID "z";

val t1 = ILAM ("x", vx);
val t2 = ILAM ("y", vx);
val t3 = IAPP (vz, IAPP (t2, t1));
val t4 = IAPP (vz, t1);
val t5 = IAPP (t3, t3);
val t6 = ILAM("x", (ILAM ("y", (ILAM ("z", IAPP( IAPP (vz, vy), IAPP (vz, vx)))))));
val t7 = IAPP( t1, IAPP (t1, t6));
val t8 = ILAM("z", IAPP( IAPP (vz, t1), vz));
val t9 = IAPP (t3, t8);

end
