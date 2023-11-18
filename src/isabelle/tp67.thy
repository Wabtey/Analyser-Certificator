theory tp67
imports Main  "~~/src/HOL/Library/Code_Target_Int" 
begin

(* Types des expressions, conditions et programmes (statement) *)
datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip
(* Un exemple d'expression *)

(* expr1= (x-10) *)
definition "expr1= (Sub (Variable ''x'') (Constant 10))"


(* Des exemples de programmes *)

(* p1= exec(0) *)
definition "p1= Exec (Constant 0)"

(* p2= {
        print(10)
        exec(0+0)
       }
*)

definition "p2= (Seq (Print (Constant 10)) (Exec (Sum (Constant 0) (Constant 0))))"

(* p3= {
         x:=0
         exec(x)
       }
*)

definition "p3= (Seq (Aff ''x'' (Constant 0)) (Exec (Variable ''x'')))"

(* p4= {
         read(x)
         print(x+1)
       }
*)
definition "p4= (Seq (Read ''x'') (Print (Sum (Variable ''x'') (Constant 1))))"


(* Le type des evenements soit X: execute, soit P: print *)
datatype event= X int | P int

(* les flux de sortie, d'entree et les tables de symboles *)

type_synonym outchan= "event list"
definition "el1= [X 1, P 10, X 0, P 20]"                   (* Un exemple de flux de sortie *)

type_synonym inchan= "int list"           
definition "il1= [1,-2,10]"                                (* Un exemple de flux d'entree [1,-2,10]              *)

type_synonym symTable= "(string * int) list"
definition "(st1::symTable)= [(''x'',10),(''y'',12)]"      (* Un exemple de table de symbole *)


(* La fonction (partielle) de recherche dans une liste de couple, par exemple une table de symbole *)
datatype 'a option= None | Some 'a

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

(* Exemples de recherche dans une table de symboles *)

value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)


(* Evaluation des expressions par rapport a une table de symboles *)
fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

(* Exemple d'évaluation d'expression *)

value "evalE expr1 st1"

(* Evaluation des conditions par rapport a une table de symboles *)
fun evalC:: "condition \<Rightarrow> symTable \<Rightarrow> bool"
where
"evalC (Eq e1 e2) t= ((evalE e1 t) = (evalE e2 t))"

(* Evaluation d'un programme par rapport a une table des symboles, a un flux d'entree et un flux de sortie. 
   Rend un triplet: nouvelle table des symboles, nouveaux flux d'entree et sortie *)
fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"
where
"evalS Skip x=x" |
"evalS (Aff s e)  (t,inch,outch)=  (((s,(evalE e t))#t),inch,outch)" |
"evalS (If c s1 s2)  (t,inch,outch)=  (if (evalC c t) then (evalS s1 (t,inch,outch)) else (evalS s2 (t,inch,outch)))" |
"evalS (Seq s1 s2) (t,inch,outch)= 
    (let (t2,inch2,outch2)= (evalS s1 (t,inch,outch)) in
        evalS s2 (t2,inch2,outch2))" |
"evalS (Read _) (t,[],outch)= (t,[],outch)" |
"evalS (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"evalS (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
"evalS (Exec e) (t,inch,outch)= 
  (let res= evalE e t in
   (t,inch,((X res)#outch)))"



(* Exemples d'évaluation de programmes *)
(* Les programmes p1, p2, p3, p4 ont été définis plus haut *)
(* p1= exec(0) *)

value "evalS p1 ([],[],[])"

(* ------------------------------------ *)
(* p2= {
        print(10)
        exec(0+0)
       }
*)

value "evalS p2 ([],[],[])"

(* ------------------------------------ *)
(* p3= {
         x:=0
         exec(x)
       }
*)

value "evalS p3 ([],[],[])"

(* ------------------------------------ *)
(* p4= {
         read(x)
         print(x+1)
       }
*)

value "evalS p4 ([],[10],[])"


definition "bad1= (Exec (Constant 0))"
definition "bad2= (Exec (Sub (Constant 2) (Constant 2)))"
definition "bad3= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x'')) (Exec (Sub (Variable ''x'') (Constant 1)))))"
definition "bad4= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) Skip (Aff ''y'' (Constant 1))) (Exec (Sum (Variable ''y'') (Constant 1)))))"
definition "bad5= (Seq (Read ''x'') (Seq (Aff ''y'' (Sum (Variable ''x'') (Constant 2))) (Seq (If (Eq (Variable ''x'') (Sub (Constant 0) (Constant 1))) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x'')))) (Seq (Aff ''x'' (Sub (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x''))))) (Exec (Variable ''y'')))))"
definition "bad6= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 1)) (Aff ''z'' (Constant 0))) (Exec (Variable ''z''))))"
definition "bad7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 1))) (Exec (Variable ''z''))))"
definition "bad8= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "ok0= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Print (Sum (Variable ''y'') (Variable ''x'')))
(Print (Variable ''x''))
) (Print (Variable ''y''))
) (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 2)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 3)) (Seq (Print (Variable ''x''))
 (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Sum (Variable ''x'') (Variable ''x''))) (Aff ''z'' (Sub (Variable ''x'') (Variable ''y'')))) (Print (Variable ''z''))
)))))))))))"
definition "ok1= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Sum (Variable ''x'') (Variable ''x'')))
 (Seq (Exec (Constant 10)) (Seq (Read ''y'') (If (Eq (Variable ''y'') (Constant 0)) (Exec (Constant 1)) (Exec (Constant 2)))))))"
definition "ok2= (Exec (Variable ''y''))"
definition "ok3= (Seq (Read ''x'') (Exec (Sum (Variable ''y'') (Constant 2))))"
definition "ok4= (Seq (Aff ''x'' (Constant 0)) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 20))) (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 4))) (Seq (Exec (Variable ''z'')) (Exec (Variable ''x''))))))"
definition "ok5= (Seq (Read ''x'') (Seq (Aff ''x'' (Constant 4)) (Exec (Variable ''x''))))"
definition "ok6= (Seq (If (Eq (Constant 1) (Constant 2)) (Aff ''x'' (Constant 0)) (Aff ''x'' (Constant 1))) (Exec (Variable ''x'')))"
definition "ok7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (If (Eq (Variable ''x'') (Constant 4)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 1)))) (Exec (Variable ''x''))))"
definition "ok8= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Exec (Sub (Variable ''x'') (Constant 3)))))"
definition "ok9= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok10= (Seq (Read ''x'') (If (Eq (Variable ''x'') (Constant 0)) (Exec (Constant 1)) (Exec (Variable ''x''))))"
definition "ok11= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Sum (Variable ''x'') (Constant 1))) Skip) (Exec (Variable ''x''))))"
definition "ok12= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''z'') (If (Eq (Variable ''z'') (Constant 0)) (Exec (Variable ''y'')) (Exec (Variable ''z'')))))"
definition "ok13= (Seq (Aff ''z'' (Constant 4)) (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (Aff ''x'' (Sum (Variable ''x'') (Sum (Variable ''z'') (Variable ''x'')))) (Seq (Aff ''z'' (Sum (Variable ''z'') (Variable ''x''))) (Seq (If (Eq (Variable ''y'') (Constant 1)) (Aff ''x'' (Sub (Variable ''x'') (Variable ''y''))) Skip) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Aff ''y'' (Sum (Variable ''y'') (Constant 1))) (Exec (Variable ''x''))) Skip) (Exec (Variable ''y'')))))))))"
definition "ok14= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"


(* v--------------------- Le TP commence ici! ---------------------v *)

(* -- 3.1 -- *)
(* p1, p2, p3 are dangerous (call a exec(0)) p4 is safe. *)

(* -- 3.2 -- *)
(*
  We dont have to test different value
  for inchan in p1, p2, p3; They don't call any read()
*)

value "evalS p1 ([],[0, 1],[])"
value "evalS p2 ([],[10],[])"
value "evalS p3 ([],[50],[])"
value "evalS p4 ([],[0],[])"
value "evalS p4 ([],[-1],[])"

(* -- 3.3 -- *)
(* p1, p2, p3 are still considered as bad, there is no exec in p4 so it's safe *)

(* -- 3.4 -- *)
fun BAD::"(symTable * inchan * outchan) \<Rightarrow> bool"
  where
  "BAD (t,inchan, outchan) = List.member outchan (X 0)"

lemma badIsBad: "List.member outchan (X 0) \<longrightarrow> BAD (t, inchan, outchan)"
  nitpick[timeout=120]
  quickcheck[tester=narrowing,size=5,timeout=120]
  apply auto
  done

(* ---------- Static Analyzer ---------- *)

(*
  Si san accepte un programme alors son évaluation,
  quelles que soient les entrées utilisateur (inchan)
  ne provoquera pas d'exec(0).
*)

(* -- 4.1 --  *)
fun sanShotgun::"statement \<Rightarrow> bool"
  where
"sanShotgun (Seq s1 s2) = (sanShotgun s1 \<and> sanShotgun s2)" |
"sanShotgun (If _ s1 s2) = (sanShotgun s1 \<and> sanShotgun s2)" |
"sanShotgun (Exec _) = False" |
"sanShotgun _ = True"

lemma correctionSanShotgun: "sanShotgun s \<longrightarrow> \<not>BAD (evalS s ([],i,[]))"
  nitpick
  quickcheck
  apply auto
  sorry

(* --- 4.2 --- *)
fun sanConstant::"statement \<Rightarrow> bool"
  where
"sanConstant (Seq s1 s2) = (sanConstant s1 \<and> sanConstant s2)" |
"sanConstant (If _ s1 s2) = (sanConstant s1 \<and> sanConstant s2)" |
"sanConstant (Exec (Constant c)) = (\<not>(c=0))" |
"sanConstant (Exec _) = False" |
"sanConstant _ = True"

lemma correctionSanConstant: "sanConstant s \<longrightarrow> \<not>BAD (evalS s ([],i,[]))"
  nitpick
  quickcheck
  apply auto
  sledgehammer
  sorry

(* --- 4.3 --- *)

(* ----- Just differenciate the Read and noneRead path ----- *)

(* TODO *)

(* ----- Visualize all possibles outcome ----- *)

fun remove::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"remove _ [] = []" |
"remove e (x#xs) = (
  if e=x then remove e xs
  else x # remove e xs
)"

fun howMany::"'a \<Rightarrow> 'a list \<Rightarrow> int"
  where
"howMany _ [] = 0" |
"howMany e (x # xs) = (
  if e = x then 1 + howMany e xs
  else howMany e xs
)"

fun removeDuplicate::"'a list \<Rightarrow> 'a list"
  where
"removeDuplicate [] = []" |
"removeDuplicate (x # xs) = (
  if List.member xs x then removeDuplicate xs
  else x # (removeDuplicate xs)
)"

lemma allThere: "
  List.member xs x \<longleftrightarrow> List.member (removeDuplicate xs) x
"
  apply (induct xs)
  apply simp
  using member_rec(1) by force

lemma noMoreDuplicate: "
  List.member xs x \<longleftrightarrow> howMany x (removeDuplicate xs) = 1
"
  apply (induct xs)
  apply simp
  apply (simp add: member_rec(2))
  sorry

(*
  Create a list of (max) xs lenght times ys length - duplicate.
  mapAllAddition xs ys \<Rightarrow> create a new list with all possible combinations by addition.
*)
fun mapAllAddition::"int list \<Rightarrow> int list \<Rightarrow> int list"
  where
"mapAllAddition [] res = []" |
"mapAllAddition (x # xs) ys = List.append (map (\<lambda>y::int. x+y)ys) (mapAllAddition xs ys)"

value "map (\<lambda> y::nat.1+y)[1,2]" 

abbreviation mapAllAdditionSet :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mapAllAdditionSet xs ys \<equiv> removeDuplicate (mapAllAddition xs ys)"

value "mapAllAdditionSet [0] [0,1,2,3]"
value "mapAllAdditionSet [1] [0,1,2,3]"
value "mapAllAdditionSet [0,1,2,3] [1]"
value "mapAllAdditionSet [0,1] [0,1,2,3]"
value "mapAllAdditionSet [10] [0,1,2,3]"
value "mapAllAdditionSet [0,1,2,3] [0,1,2,3]"
value "mapAllAdditionSet [1,0,11] [2,1,5]"
value "mapAllAdditionSet [] [2,1,1,5]"

(* TODO: Lemmas on mapAllAdditionSet lmao... *)


(*
  Create a list of (max) xs lenght times ys length - duplicate.
  mapAllSubtraction xs ys \<Rightarrow>
    create a new list with
    all possible combinations of xs - all element of ys.
*)
fun mapAllSubtraction::"int list \<Rightarrow> int list \<Rightarrow> int list"
  where
"mapAllSubtraction [] res = []" |
"mapAllSubtraction (x # xs) ys = List.append (map (\<lambda>y::int. x-y)ys) (mapAllSubtraction xs ys)"

value "map (\<lambda> y::nat. 5-y)[1,2]" 

abbreviation mapAllSubtractionSet :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mapAllSubtractionSet xs ys \<equiv> removeDuplicate (mapAllSubtraction xs ys)"

value "mapAllSubtractionSet [0] [0,1,2,3]"
value "mapAllSubtractionSet [1] [0,1,2,3]"
value "mapAllSubtractionSet [0,1,2,3] [1]"
value "mapAllSubtractionSet [0,1] [0,1,2,3]"
value "mapAllSubtractionSet [10] [0,1,2,3]"
value "mapAllSubtractionSet [0,1,2,3] [0,1,2,3]"
value "mapAllSubtractionSet [1,0,11] [2,1,5]"
value "mapAllSubtractionSet [] [2,1,1,5]"

type_synonym staticSymTable= "(string * (int option) list) list"
(* Un exemple de table de symbole *)
definition "(statST1::staticSymTable)=
  [
    (''x'',[Some 5, Some 0]),
    (''y'',[None, Some 2, Some 17])
  ]"
definition "(statST2::staticSymTable)=
  [
    (''x'',[Some 1]),
    (''z'',[Some 7, None])
  ]"

fun removeStatST::"string \<Rightarrow> staticSymTable \<Rightarrow> staticSymTable" where
  "removeStatST _ [] = []" |
  "removeStatST e ((var, values)#xs) = (
    if e = var then removeStatST e xs
    else (var, values)#(removeStatST e xs)
  )"

(* Search e in *)
fun staticAssoc:: "'a \<Rightarrow> ('a * ('b option) list) list \<Rightarrow> ('b option) list"
where
"staticAssoc _ [] = []" |
"staticAssoc e ((y,ys)#xs)= (if e=y then ys else (staticAssoc e xs))"

fun mergeStatST::"staticSymTable \<Rightarrow> staticSymTable \<Rightarrow> staticSymTable"
  where
"mergeStatST [] ys = ys" |
"mergeStatST ((var, varsX) # xs) ys = (
  let varsY = staticAssoc var ys in
    (var, List.append varsX varsY) # mergeStatST xs (removeStatST var ys)
)"

value "mergeStatST statST1 statST2"

(* Exemples de recherche dans une table de symboles *)
value "staticAssoc ''x'' statST1"     (* quand la variable est dans la table statST1 *)
value "staticAssoc ''z'' statST1"     (* quand la variable n'est pas dans la table statST1 *)

(*
  Evaluation des expressions
  par rapport a une table de symboles custom.

  \<Rightarrow> (int list) option
*)
fun staticEvalE:: "expression \<Rightarrow> staticSymTable \<Rightarrow> int list"
where
"staticEvalE (Constant c) _ = [c]" |

"staticEvalE (Sum e1 e2) e= (mapAllAdditionSet (staticEvalE e1 e) (staticEvalE e2 e))" |
"staticEvalE (Sub e1 e2) e= (mapAllSubtractionSet (staticEvalE e1 e) (staticEvalE e2 e))" |
(* TODO: staticEvalE (Variable s) e *)
"staticEvalE (Variable s) e= (
  let ys = (staticAssoc s e) in (
    if (List.member ys None) then [-1]
    else (
      [0,0]
    ) 
))"
(* staticEvalE (Variable s) e = "(case (staticAssoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" *)

fun san::"statement \<Rightarrow> staticSymTable \<Rightarrow> (staticSymTable * bool)"
  where
"san (Seq s1 s2) symt = (
  let (s1ST, s1IsOK) = san s1 symt in
    let (s2ST, s2IsOK) = san s2 s1ST in
      (s2ST, s1IsOK \<and> s2IsOK)
)" |
(* TODO: draw all possible staticSymTable for each arm and return the concat of the two *)
"san (If c s1 s2) symt = (
  let (s1ST, s1IsOK) = san s1 symt in
    let (s2ST, s2IsOK) = san s2 symt in
      (s2ST, s1IsOK \<and> s2IsOK)
)" |
(* v---------------v *)
(*
"san (Aff s e) symt =  (s,(evalE e t)#t)" |
"san (Read _) (t,[],outch)= (t,[],outch)" |
"san (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"san (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
*)
(* ^---------------^ *)
(* TODO:
"san (Exec e) symt = (\<not>(staticEvalE e symt = 0))" |
*)
"san _ _ = ([],False)"
(* true end: "san _ _ = (?, True)" *)

(* TODO: Lemma *)
lemma correctionSan: "
  let (sST, isOK) = san s [] in isOK \<longrightarrow> \<not>BAD (evalS s ([],i,[]))"
  nitpick
  quickcheck
  apply auto
  sledgehammer
  sorry

(* ----- Restriction de l'export Scala (Isabelle 2018) -------*)
(* ! ! !  NE PAS MODIFIER ! ! ! *)
(* Suppression de l'export des abstract datatypes (Isabelle 2018) *)
code_reserved Scala
  expression condition statement 
code_printing
   type_constructor expression \<rightharpoonup> (Scala) "expression"
  | constant Constant \<rightharpoonup> (Scala) "Constant"
  | constant Variable \<rightharpoonup> (Scala) "Variable"
  | constant Sum \<rightharpoonup> (Scala) "Sum"
  | constant Sub \<rightharpoonup> (Scala) "Sub"  

  | type_constructor condition \<rightharpoonup> (Scala) "condition"
  | constant Eq \<rightharpoonup> (Scala) "Eq"

  | type_constructor statement \<rightharpoonup> (Scala) "statement"
  | constant Seq \<rightharpoonup> (Scala) "Seq"
  | constant Aff \<rightharpoonup> (Scala) "Aff"
  | constant Read \<rightharpoonup> (Scala) "Read"
  | constant Print \<rightharpoonup> (Scala) "Print"
  | constant Exec \<rightharpoonup> (Scala) "Exec"
  | constant If \<rightharpoonup> (Scala) "If"
  | constant Skip \<rightharpoonup> (Scala) "Skip"
  | code_module "" \<rightharpoonup> (Scala) 
\<open>// Code generated by Isabelle
package tp67

import utilities.Datatype._
import scala.language.implicitConversions

// automatic conversion of utilities.Datatype.Int.int to Int.int
object AutomaticConversion{ 
	implicit def int2int(i:utilities.Datatype.Int.int):Int.int =
			i match {
			case utilities.Datatype.Int.int_of_integer(i)=>Int.int_of_integer(i)
	}
	
	def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
  (if (k == BigInt(0)) (BigInt(0), false)
    else {
           val (r, s): (BigInt, BigInt) =
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(BigInt(2));
           ((if (BigInt(0) < k) r else (- r) - s), s == BigInt(1))
         })
         
	def char_of_integer(k: BigInt): String.char =
  {
    val (q0, b0): (BigInt, Boolean) = bit_cut_integer(k)
    val (q1, b1): (BigInt, Boolean) = bit_cut_integer(q0)
    val (q2, b2): (BigInt, Boolean) = bit_cut_integer(q1)
    val (q3, b3): (BigInt, Boolean) = bit_cut_integer(q2)
    val (q4, b4): (BigInt, Boolean) = bit_cut_integer(q3)
    val (q5, b5): (BigInt, Boolean) = bit_cut_integer(q4)
    val (q6, b6): (BigInt, Boolean) = bit_cut_integer(q5)
    val a: (BigInt, Boolean) = bit_cut_integer(q6)
    val (_, aa): (BigInt, Boolean) = a;
    String.Chara(b0, b1, b2, b3, b4, b5, b6, aa)
  }
	
  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil) => Nil
    case (f, x :: xs) => f(x) :: map[A, B](f, xs)
  }

	def explodeList(l: List[Char]): List[String.char] ={
       (l.map(c => { val k: Int = c.toInt; if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal") })).map(a => char_of_integer(a))
    }
	
	def explode(s: String): List[String.char] ={
	    explodeList(s.toCharArray.toList)
	}
	
	// conversion from Scala String to HOL string
  implicit def string2charList(s:String):List[String.char]= explode(s)
  
  // conversion from Scala List[Char] to HOL List[String.char]
  implicit def charList2charList(l:List[Char]):List[String.char]= explodeList(l)
  // conversion of a pair with a Scala List[String] on the first position
  // to an HOL pair with an HOL List[String.char] on first position
	implicit def tupleString2tupleString[T](t:(List[Char],T)):
	    (List[String.char],T)= t match { case (e1,e2) => (charList2charList(e1),e2)}

  // conversion from Isabelle Int.int to Project Int.int
  implicit def int2Dataint(i:Int.int):utilities.Datatype.Int.int =
            i match {
            case Int.int_of_integer(i)=>utilities.Datatype.Int.int_of_integer(i)
    }

   def stringChar2char(x: String.char): Char = {
        x match {
          case String.Chara(x1,x2,x3,x4,x5,x6,x7,x8) => {
            var n = 0;
            n = if (x8) 2*n+1 else 2*n;
            n = if (x7) 2*n+1 else 2*n;
            n = if (x6) 2*n+1 else 2*n;
            n = if (x5) 2*n+1 else 2*n;
            n = if (x4) 2*n+1 else 2*n;
            n = if (x3) 2*n+1 else 2*n;
            n = if (x2) 2*n+1 else 2*n;
            n = if (x1) 2*n+1 else 2*n;
            n.toChar
          }
        }
      }

    // conversion from Isabelle String to Lists of Chars
    implicit def charList2String(l: List[String.char]): List[Char] = {
          l.map(stringChar2char(_))
    } 
}

import AutomaticConversion._
\<close>



(* Directive pour l'exportation de l'analyseur *)

(* TODO: URGENT - change to san to export the finest one *)
export_code sanConstant in Scala (case_insensitive)

(* file "~/workspace/TP67/src/tp67/san.scala"   (* à adapter en fonction du chemin de votre projet TP67 *)
*)

end
