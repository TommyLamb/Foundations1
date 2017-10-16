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

end
