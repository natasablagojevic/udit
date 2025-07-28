theory stekmasina
  imports Main 

begin 

datatype izraz =  Const nat
  | Plus izraz izraz 
  | Minus izraz izraz 
  | Puta izraz izraz 

term "Plus (Const 3) (Const 2)"

primrec vrednost:: "izraz \<Rightarrow> nat" 
  where "vrednost (Const x) = x"
  | "vrednost (Plus x1 x2) = (vrednost x1) + (vrednost x2)"
  | "vrednost (Minus x1 x2) =(vrednost x1) - (vrednost x2)"
  | "vrednost (Puta x1 x2) = (vrednost x1) * (vrednost x2)"

type_synonym stek = "nat list"

datatype operacija = OpPlus
  | OpMinus 
  | OpPuta 
  | OpPush nat

fun izvrsiOp:: "operacija \<Rightarrow> stek \<Rightarrow> stek"
  where "izvrsiOp (OpPush x) xs = x # xs"
  | "izvrsiOp OpMinus (x1 # x2 # xs) = (x1-x2)#xs"
  | "izvrsiOp OpPlus (x1 # x2 # xs) = (x1+x2)#xs"
  | "izvrsiOp OpPuta (x1 # x2 # xs) = (x1*x2)#xs"

type_synonym program = "operacija list"

fun prevedi:: "izraz \<Rightarrow> program"
  where "prevedi (Const x) = [OpPush x]"
  | "prevedi (Plus x1 x2) = OpPlus # (prevedi x1) @ (prevedi x2)"
  | "prevedi (Minus x1 x2) = OpMinus # (prevedi x1) @ (prevedi x2)"
  | "prevedi (Puta x1 x2) = OpPuta # (prevedi x1) @ (prevedi x2)"

definition x1:: "izraz"
  where "x1 \<equiv> Plus (Const 2) (Const 3)"

definition x2:: "izraz"
  where "x2 \<equiv> Puta (Const 3) (Minus (Const 5) (Const 2))"

definition x3:: "izraz"
  where "x3 \<equiv> Puta (Const 3) (Puta (Const 4) (Minus (Const 5) (Const 2)))"


value "vrednost x1"
value "vrednost x2"
value "vrednost x3"

value "x1"
value "prevedi x1"

value "x2"
value "prevedi x2"

value "x3"
value "prevedi x3"

primrec izvrsiProgram:: "program \<Rightarrow> stek \<Rightarrow> stek"
  where "izvrsiPorgram [] stek = stek"
  | "izvrsiProgram (op#program) stek = izvrsiOp op (izvrsiProgram program stek)"

value "izvrsiPorgram (prevedi x1) []"


end