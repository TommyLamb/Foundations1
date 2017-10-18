structure Combinatorics = struct

fun printEXP (CID v) = print v
  | printEXP (CI) = print "I''"
  | printEXP (CS) = print "S''"
  | printEXP (CK) = print "K''"
  | printEXP (CAPP (a, b)) = (
	print "("; 
	printEXP a;
	printEXP b;
	print ")"
	);

fun isRedex (CAPP (CI, v)) = true
  | isRedex (CAPP ((CAPP (CK, v1)), v2)) = true 
  | isRedex (CAPP ((CAPP ((CAPP (CS, v1)), v2)), v3)) = true
  | isRedex _ = false;

fun hasRedex (CAPP (x, y)) = (isRedex (CAPP (x, y))) orelse hasRedex x orelse hasRedex y 
  | hasRedex _ = false;

fun appToList expression [] = []
  | appToList expression (hd::tl) = (CAPP (expression, hd))::(appToList expression tl);

fun appFromList [] expression = []
  | appFromList (hd::tl) expression = (CAPP (hd, expression))::(appFromList tl expression);

fun red (CAPP (CI, v)) = v
  | red (CAPP ((CAPP (CK, v1)), v2)) = v1 
  | red (CAPP ((CAPP ((CAPP (CS, v1)), v2)), v3)) = CAPP ((CAPP ( v1, v3)), (CAPP ( v2, v3)));

  (* For comments see Lamda.leftmost *)
fun reduce (CID v) = [CID v]
  | reduce (CI) = [CI]
  | reduce (CK) = [CK]
  | reduce (CS) = [CS]
  | reduce (CAPP (a, b)) = 
	if (isRedex (CAPP(a, b))) then
		(CAPP(a, b))::(reduce (red (CAPP(a, b))))
	else if (isRedex a) then
		(CAPP(a, b))::(reduce (CAPP ((red a), b)))
	else if (isRedex b) then	
		(CAPP(a, b))::(reduce (CAPP (a, (red b))))
	else if (hasRedex a) then
		let 
			val abreduction = (appFromList (reduce a) b)
		in
			abreduction@(tl (reduce (List.last abreduction)))
		end
	else if (hasRedex b) then
		appToList a (reduce b)
	else
		[CAPP (a, b)];
  

		
fun printReduction [] = print "\n"
  | printReduction (hd::[]) = (printEXP hd; print "\n")
  | printReduction (hd::tl) = (printEXP hd; print " -->\n"; printReduction tl);
  

fun printReductionCount x = (
		printReduction x;
		print "Steps: ";
		print (Int.toString((List.length x)-1));
		print "\n"
		);
  
fun subtermsList (CID v) = [CID v]
  | subtermsList (CI) = [CI]
  | subtermsList (CK) = [CK]
  | subtermsList (CS) = [CS]
  | subtermsList (CAPP (a, b)) = [CAPP (a, b)]@(subtermsList a)@(subtermsList b);

  
fun setify [] = []
  | setify (hd::tl) = 
	if (List.exists (fn x => hd = x) tl) then
		setify tl
	else
		hd::setify tl;

fun subterms x = setify (subtermsList x);

(* Note that SML will type this COM -> COM -> bool, even if every clause was (CID id) (COM). Thus it whines about
non exhaustive matches without the wildcard clause *)
fun free (CID id) (CID x) = (id = x)
  | free (CID id) (CAPP (a, b)) = (free (CID id) a) orelse (free (CID id) b) 
  | free _ _ = false;


val red3 =  (CAPP ((CAPP ((CAPP (CS, CID "v1")), CID "v2")), CID "v3"));


val vx = CID "x";
val vy = CID "y";
val vz = CID "z";

val t1 = CI;
val t2 = CAPP (CK, vx);
val t3 = CAPP (CAPP (CI, CAPP (CK, vx)), vz);
val t4 = CAPP (CI, vz);
val t5 = CAPP (CAPP (CAPP (CI, CAPP (CK, vx)), vz), CAPP (CAPP (CI, CAPP (CK, vx)), vz));
val t6 = CS;
val t7 = CAPP (CAPP (CS, CI), CI);
val t8 = CAPP (CAPP (CS, CI), CI);
val t9 = CAPP (CAPP (CAPP (CS, CI), CI), CAPP (CAPP (CI, CAPP (CK, vz)), vz));
val omega = CAPP (CAPP (CAPP (CS, CI), CI), CAPP (CAPP (CS, CI), CI));

val list = [vx, vy, vz, t1, t2, t3, t4, t5, t6, t7, t8, t9];



end
