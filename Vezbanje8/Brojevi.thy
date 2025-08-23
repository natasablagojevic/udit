theory Brojevi 
  imports Main

begin


datatype integer = 
  Zero ("\<zero>")
  | Pos nat 
  | Neg nat 

abbreviation posone:: integer ("+\<one>") where "+\<one> \<equiv> Pos 0"
abbreviation postwo:: integer ("+\<two>") where "+\<two> \<equiv> Pos 1"
abbreviation negone:: integer ("-\<one>") where "-\<one> \<equiv> Neg 0"
abbreviation negtwo:: integer ("-\<two>") where "-\<two> \<equiv> Neg 1"

fun neg:: "integer \<Rightarrow> integer" 
  where "neg Zero = Zero"
  | "neg (Pos n) = Neg n"
  | "neg (Neg n) = Pos n"


lemma "neg (neg n) = n"
  by (induction n) auto 

fun succ:: "integer \<Rightarrow> integer" 
  where "succ Zero = Pos 0"
  | "succ (Pos n) = Pos (Suc n)"
  | "succ (Neg 0) = Zero"
  | "succ (Neg (Suc n)) = Neg n"

fun pred:: "integer \<Rightarrow> integer"
  where "pred Zero = Neg 0"
  | "pred (Pos 0) = Zero"
  | "pred (Pos (Suc n)) = Pos n"
  | "pred (Neg n) = Neg (Suc n)"


fun leq:: "nat \<Rightarrow> nat \<Rightarrow> bool" (infixl "\<sqsubseteq>" 100)
  where "leq m n = (m \<le> n)"

lemma refleksivnost: 
  shows "\<forall>x. x \<sqsubseteq> x"
  by auto 

lemma tranzitivnost:
  shows "\<forall>x y z. x \<sqsubseteq> y \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z" 
  by auto 

lemma antisimetricnost:
  shows "\<forall>x y. x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longrightarrow> x = y"
  by auto 




end