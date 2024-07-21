theory cas3 
  imports Main

begin

(*
  Ako onaj ko laze taj i krade i ako bar neko laze, onda neko i krade.

  laze(x) = x laze 
  krade(x) = x krade

  (\<forall>x. laze x \<and> krade x) \<and> (\<exists>x. laze x) \<longrightarrow> (\<exists>x . krade x)

*)

lemma "(\<forall>x. laze x \<and> krade x) \<and> (\<exists>x. laze x) \<longrightarrow> (\<exists>x . krade x)"
  by auto

(*
  Ako "ko radi taj ima ili trosi" i "ko ima taj peva" i "ko trosi taj peva", onda "ko radi taj peva".
  
  radi(x) = x radi 
  trosi(x) = x trosi 
  peva(x) = x peva 

  (\<forall>x. radi x \<longrightarrow> (ima x \<or> trosi x)) \<and> (\<forall>x. ima x \<longrightarrow> peva x) \<and> (\<forall>x. trosi x \<longrightarrow> peva x) \<longrightarrow> (\<forall>x. radi x \<longrightarrow> peva x)

*)

lemma "(\<forall>x. radi x \<longrightarrow> (ima x \<or> trosi x)) \<and> (\<forall>x. ima x \<longrightarrow> peva x) \<and> (\<forall>x. trosi x \<longrightarrow> peva x) \<longrightarrow> (\<forall>x. radi x \<longrightarrow> peva x)"
  by auto 

(*

Ako je X prijatelj osobe Y, onda je i Y prijatelj osobe X.
Ako je X prijatelj osobe Y, onda X voli Y.
Ne postoji neko ko je povredio osobu koju voli.
Osoba Y je povredila svog prijatelja X.

prijatelj(x, y) = x je prijatelj od y 
voli(x, y) = x voli y 
povredio(x, y) = x je povredio y

(\<forall>x y. prijatelj x y \<longrightarrow> prijatelj y x)
(\<forall>x y. prijatelj x y \<longrightarrow> voli x y)
\<not>(\<exists>x y. voli x y \<and> povredio x y)
(\<exists>x y. povredio y x) 


*)
lemma "(\<forall>x y. prijatelj x y \<longrightarrow> prijatelj y x) 
      \<and> (\<forall>x y. prijatelj x y \<longrightarrow> voli x y) 
      \<and> (\<not>(\<exists>x y. voli x y \<and> povredio x y)) 
      \<and> (\<exists>x y. prijatelj y x \<and> povredio y x) \<longrightarrow> False"
  by auto 

(* --------------------------------------------------------------------------------------------- *)

(*
Ako ”šta leti to ima krila i lagano je” i ”šta pliva, to nema krila”, onda ”šta pliva, to ne leti”.

leti(x) = x leti 
krila(x) = x ima krila 
lagano(x) = x je lagano 
pliva(x) = x pliva 

(\<forall>x. leti x \<longrightarrow> krila x \<and> lagano je) \<and> (\<forall>x. pliva x \<longrightarrow> \<not> krila x) \<longrightarrow> (\<forall>x. pliva x \<longrightarrow> \<not> leti x)

*)

lemma "(\<forall>x. leti x \<longrightarrow> krila x \<and> lagano je) \<and> (\<forall>x. pliva x \<longrightarrow> \<not> krila x) \<longrightarrow> (\<forall>x. pliva x \<longrightarrow> \<not> leti x)"
  by auto

(* ---------------------------------------------------------------------------------------------- *)

(*

X cipela, Y noga, Z trenutak

Ako postoji cipela koja u svakom trenutku odgovara svakoj nozi,
(\<exists>x. \<forall>z. \<forall> y. P x y z)


onda za svaku nogu postoji cipela koja joj u nekom trenutku odgovara i 
(\<forall>y. \<exists>x. \<exists>z. P x y z)


za svaku nogu postoji trenutak takav da postoji cipela koja joj u tom trenutku odgovara.
(\<forall>y. \<exists>z. \<exists>x. P x y z)

*)

lemma "(\<exists>x. \<forall>z. \<forall> y. P x y z) \<longrightarrow> ((\<forall>y. \<exists>x. \<exists>z. P x y z) \<and> (\<forall>y. \<exists>z. \<exists>x. P x y z))"
  by auto

(* ---------------------------------------------------------------------------------------------- *)

(*
Svako ko je srećan voli da peva.
Svako ko voli da peva, voli da pleše.
Andrija je srećan.

posledica: Andrija voli da pleše.

srecan(x) = x je srecan 
peva(x) = x voli da peva 
plese(x) = x voli da plese 
------------------------------

(\<forall>x. srecan x \<longrightarrow> peva x)
(\<forall>x. peva x \<longrightarrow> plese x)
srecan Andrija

\<longrightarrow> plese Andrija

*)

lemma "(\<forall>x. srecan x \<longrightarrow> peva x) \<and> (\<forall>x. peva x \<longrightarrow> plese x) \<and> srecan Andrija \<longrightarrow> plese Andrija"
  by auto

(* ---------------------------------------------------------------------------------------------- *)

(*
Svaki dečak voli da se igra.
Svaka devojčica voli da se igra.
Dete je dečak ili je devojčica.

\<longrightarrow> Svako dete voli da se igra.

------------------------------------

decak(x) = x je decak 
devojcica(x) = x je devojcica 
igra(x) = x voli da se igra 
dete(x) = x je dete 

----------------------------------

(\<forall>x. decak x \<longrightarrow> igra x)
(\<forall>x. devojcica x \<longrightarrow> igra x)
(\<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x)

\<longrightarrow> (\<forall>x. dete x \<longrightarrow> igra x)

*)


lemma "(\<forall>x. decak x \<longrightarrow> igra x) 
      \<and> (\<forall>x. devojcica x \<longrightarrow> igra x)
      \<and> (\<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x) 
      \<longrightarrow> (\<forall>x. dete x \<longrightarrow> igra x)"
  by auto

(* ---------------------------------------------------------------------------------------------- *)

(*
  POKAZATI DA SU SLEDECE FORMULE NEZADOVOLJIVE:

Svaka dva brata imaju zajedničkog roditelja.
Roditelj je stariji od deteta.
Postoje braća.
Nijedna osoba nije starija od druge.

\<longrightarrow> False 

------------------------------------------------------

brat(x, y) = x je brat od y 
roditelj(x, y) = x je roditelj od y 
starija(x, y) = x je stariji od y

-----------------------------------------------------

(\<forall>x. \<forall> y. brat x y \<longrightarrow> (\<exists>z. roditelj z x \<and> roditelj z y))
(\<forall>x. \<forall>y. roditelj x y \<longrightarrow> stariji x y)
(\<exists>x. \<exists>y. brat x y)
(\<exists>x. \<exists>y. \<not> stariji x y)

\<longrightarrow> False 
*)

lemma "(\<forall>x. \<forall> y. \<exists>z.  brat x y \<longrightarrow> roditelj z x \<and> roditelj z y)
  \<and> (\<forall>x. \<forall>y. roditelj x y \<longrightarrow> stariji x y)
  \<and> (\<exists>x. \<exists>y. brat x y) 
  \<and> (\<not>(\<exists>x. \<exists>y. stariji x y)) \<longrightarrow> False"
  by auto

(* ---------------------------------------------------------------------------------------------- *)

lemma "(\<forall>x. men x \<longrightarrow> mortal x)
  \<and> (\<forall>x. greek x \<longrightarrow> men x)
  \<longrightarrow> (\<forall>x. greek x \<longrightarrow> mortal x)"
  by auto 

lemma "(\<nexists>x. reptile x \<and> fur x) \<and> (\<forall>x. snake x \<longrightarrow> reptile x) \<longrightarrow> (\<nexists>x. snake x \<and> fur x)"
  by auto 

lemma "(\<nexists>x. homework x \<and> fun x) \<and> (\<exists>x. reading x \<and> homework x) \<longrightarrow> (\<exists>x. reading x \<and> \<not> fun x)"
  by auto 

lemma "(\<exists>x. cat x \<and> \<not> pet x) \<and> (\<forall>x. cat x \<longrightarrow> mamal x) \<longrightarrow> (\<exists>x. mamal x \<and> \<not> pet x)"
  by auto 

lemma "(\<forall>x. horse x \<longrightarrow> hoove x) \<and> (\<nexists>x. human x \<and> hoove x) \<and> (\<exists>x. human x) \<longrightarrow> (\<exists>x. human x \<and> \<not> horse x)"
  by auto 

(* ---------------------------------------------------------------------------------------------- *)

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done 

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption 
  apply (rule disjI1)
  apply assumption 
  done 

lemma "A \<and> B \<longrightarrow> A \<or> B"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done 

lemma "((A \<or> B) \<and> \<not>A) \<longrightarrow> B"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
  sorry 

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply (rule impI) +
  apply (erule impE)
   apply (rule conjI)
    apply (assumption) +
  done

lemma "(A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> (A \<and> B \<longrightarrow> C)"
  apply (rule impI)+
  apply (erule impE)+
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply (erule impE)
   apply (assumption) +
  done 

lemma "\<not>(A \<or> B) \<longrightarrow> \<not>A \<and> \<not>B"
  apply (rule impI)
  apply (rule conjI)
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done 

lemma "\<not>A \<and> \<not>B \<longrightarrow> \<not>(A \<or> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE)
  apply (erule notE)
  apply assumption
  done 

lemma "\<not>(A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back 
   apply (rule notI)
   apply (erule impE)
    apply assumption 
   apply (erule notE)
   apply assumption 
  apply (erule impE)
   apply (assumption)
  apply (erule notE)
  apply assumption 
  done 

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  apply (rule impI)
  apply (rule iffI)
   apply (erule conjE) +
   apply (erule impE) back back
    apply (assumption)
   apply (erule disjE) 
    apply assumption
   apply (erule impE) back 
    apply (assumption)
   apply (erule conjE)
   apply (assumption)
  apply (erule conjE)+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule conjE)
  apply assumption 
  done 

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  apply (rule impI)
  apply (rule impI)
  apply (rule conjI)
   apply (erule conjE)
   apply (erule impE)
    apply assumption
   apply assumption 
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption
  done 

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  apply (rule impI)
  apply (rule impI) +
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption 
  apply assumption 
  done 

lemma "\<not> (P \<and> \<not>P )"
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption 
  done 

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B ) \<or> (A \<and> C )"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption 
   apply assumption
  apply (rule disjI2)
  apply (rule conjI)
   apply assumption 
  apply assumption 
  done 

lemma "\<not> (A \<and> B ) \<longrightarrow> (A \<longrightarrow> \<not> B )"
  apply (rule impI)
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI)
   apply assumption +
  done 

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B )"
  apply (rule impI)
  apply (erule conjE)
  apply (rule notI)
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule conjE)
  apply (erule notE)
  apply assumption 
  done 

lemma "(A \<and> B ) \<longrightarrow> ((A \<longrightarrow> C ) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C ))"
  apply (rule impI)
  apply (rule impI)
  apply (rule notI)
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule notE)
  apply assumption
  done 

lemma "(A \<longleftrightarrow> B ) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B )"
  apply (rule impI)
  apply (rule iffI)
   apply (rule notI)
   apply (erule iffE)
   apply (erule notE)
  apply (erule impE) +
     apply assumption +
   apply (erule impE)
    apply assumption +
  apply (rule notI)
  apply (erule iffE)
  apply (erule notE)
  apply (erule impE)
   apply assumption +
  done 

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption 
  done 

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back
   apply (rule notI)
   apply (erule impE)
    apply assumption 
   apply (erule notE)
   apply assumption 
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "(A \<longrightarrow> B ) \<longrightarrow> (\<not> B \<longrightarrow> \<not> A)"
  apply (rule impI)
  apply (rule impI)
  apply (rule notI)
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "\<not> A \<or> B \<longrightarrow> (A \<longrightarrow> B )"
  apply (rule impI)
  apply (rule impI)
  apply (erule disjE)
   apply(erule notE)
   apply assumption + 
  done 

lemma "(\<forall> x . Man x \<longrightarrow> Mortal x ) \<and> Man Socrates \<longrightarrow> Mortal Socrates"
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x = "Socrates" in allE)
  apply (erule impE)
   apply assumption +
  done 

lemma "(\<exists> x . \<not> P x ) \<longrightarrow> \<not> (\<forall> x . P x )"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption +
  done 

lemma "(\<forall> x . \<not> P x ) \<longrightarrow> (\<nexists> x . P x )"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption 
  done 

lemma "(\<nexists> x . P x ) \<longrightarrow> (\<forall> x . \<not> P x )"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac x = "x" in exI)
  apply assumption 
  done 

lemma "(\<exists> x . P x ) \<and> (\<forall> x . P x \<longrightarrow> Q x ) \<longrightarrow> (\<exists> x . Q x )"
  apply (rule impI)
  apply (erule conjE)
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption +
  done 

lemma "(\<forall> m. Man m \<longrightarrow> Mortal m) \<and> (\<forall> g. Greek g \<longrightarrow> Man g) \<longrightarrow> (\<forall> a. Greek a \<longrightarrow> Mortal a)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x = "a" in allE) +
  apply (erule impE) + 
    apply assumption +
  done 

(* ccontr *)

lemma "A \<longrightarrow> \<not>\<not>A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption 
  done 

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply assumption 
  done 

lemma "(\<not> P \<longrightarrow> P ) \<longrightarrow> P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "\<not> (A \<and> B ) \<longrightarrow> \<not> A \<or> \<not> B"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule conjI)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption 
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption 
  done 

lemma "P \<or> \<not> P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption 
  done 

lemma "(A \<longleftrightarrow> (A \<longleftrightarrow> B )) \<longrightarrow> B"
  apply (rule impI)
  apply (cases A)
  apply (erule iffE) 
   apply (erule impE) 
  apply assumption
   apply (erule impE) 
    apply assumption 
   apply (erule iffE)
   apply (erule impE)
    apply assumption +
  apply (rule ccontr)
  apply (erule iffE)
  apply (erule impE)
  apply (erule notE)
   apply (erule impE)
  oops

(* ----------------------- ISAR STRUKTUIRANI DOKAZI --------------------------------------------  *)

lemma "-(A \<union> B ) = - A \<inter> - B"
proof 
  show "- (A \<union> B) \<subseteq> - A \<inter> - B"
  proof 
    fix x 
    assume "x \<in> -(A \<union> B)"
    then have "x \<notin> A \<union> B" by simp 
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<in> -A \<and> x \<in> -B" by simp 
    then show "x \<in> (-A \<inter> -B)" by simp 
  qed
next 
  show "- A \<inter> - B \<subseteq> - (A \<union> B)"
  proof 
    fix x 
    assume "x \<in> -A \<inter> -B"
    then have "x \<in> -A \<and> x \<in> -B" by simp 
    then have "x \<notin> A \<and> x \<notin> B" by simp 
    then have "x \<notin> A \<union> B" by simp 
    then show "x \<in> - (A \<union> B)" by simp 
  qed
qed

lemma "A \<union> B = B \<union> A"
proof 
  show "A \<union> B \<subseteq> B \<union> A"
  proof 
    fix x
    assume "x \<in> A \<union> B" 
    then have "x \<in> A \<or> x \<in> B" by simp 
    then have "x \<in> B \<or> x \<in> A" using disj_commute by simp 
    then show "x \<in> B \<union> A" by simp 
  qed

next 
  show "B \<union> A \<subseteq> A \<union> B"
  proof
    fix x 
    assume "x \<in> B \<union> A" 
    then have "x \<in> B \<or> x \<in> A" by simp 
    then have "x \<in> A \<or> x \<in> B" using disj_commute by simp 
    then show "x \<in> A \<union> B" by simp 
  qed
qed

lemma "A \<union> (B \<inter> C ) = (A \<union> B ) \<inter> (A \<union> C )"
proof 
  show "A \<union> (B \<inter> C) \<subseteq> (A \<union> B) \<inter> (A \<union> C)"
  proof
    fix x
    assume "x \<in> A \<union> (B \<inter> C)"
    then have "x \<in> A \<or> x \<in> B \<inter> C" by simp 
    then have "x \<in> A \<or> (x \<in> B \<and> x \<in> C)" by simp 
    then have "(x \<in> A \<or> x \<in> B) \<and> (x \<in> A \<or> x \<in> C)" using disj_conj_distribL  by simp 
    then have "x \<in> (A \<union> B) \<and> x \<in> (A \<union> C)" by simp 
    then show "x \<in> (A \<union> B) \<inter> (A \<union> C)" by simp 
  qed

next 
  show "(A \<union> B ) \<inter> (A \<union> C ) \<subseteq> A \<union> (B \<inter> C )"
  proof 
    fix x
    assume "x \<in> (A \<union> B) \<inter> (A \<union> C)"
    then have "x \<in> (A \<union> B) \<and> x \<in> (A \<union> C)" by simp 
    then have "(x \<in> A \<or> x \<in> B) \<and> (x \<in> A \<or> x \<in> C)" by simp 
    then have "x \<in> A \<or> (x \<in> B \<and> x \<in> C)" by blast
    then have "x \<in> A \<or> x \<in> (B \<inter> C)" by simp 
    then show "x \<in> A \<union> (B \<inter> C)" by simp 
  qed
qed 


lemma
  assumes "\<forall>x. (Knight x \<longrightarrow> \<not>Liar x) \<and> (Liar x \<longrightarrow> \<not>Knight x)"
  assumes "Knight A \<and> Liar B"
  assumes "A_says: A_is_Liar \<or> (A_is_Knight \<and> B_is_Liar)"
  shows "A_is_Liar \<and> B_is_Knight"
proof -
  from \<open>Knight A \<and> Liar B\<close> have A_is_Knight: "Knight A" and B_is_Liar: "Liar B" by auto
  from A_says have "A_is_Liar \<or> (A_is_Knight \<and> B_is_Liar)" by auto
  with A_is_Knight have "A_is_Liar" by auto
  with B_is_Liar show ?thesis by auto
qed


lemma
  assumes "(\<exists> x. P x )"
      and "(\<forall> x . P x \<longrightarrow> Q x )"
    shows "(\<exists> x . Q x )"
proof - 
  from assms(1) obtain x where "P x" by (erule exE)
  moreover
  from assms(2) have "P x \<longrightarrow> Q x" by (erule_tac x="x" in allE)
  ultimately
  have "Q x" by - (erule impE, assumption)
  then show "\<exists>x. Q x" by (rule_tac x = "x" in exI)
qed

lemma 
   assumes "\<forall> c. Man c \<longrightarrow> Mortal c"
       and "\<forall> g. Greek g \<longrightarrow> Man g"
     shows "\<forall> a. Greek a \<longrightarrow> Mortal a"
proof 
  fix Socrates 
  show "Greek Socrates \<longrightarrow> Mortal Socrates"
  proof 
    assume "Greek Socrates"
    moreover 
    from assms(2) have "Greek Socrates \<longrightarrow> Man Socrates" by (erule_tac x = "Socrates" in allE)
    ultimately
    have "Man Socrates" by - (erule impE, assumption)
    moreover
    from assms(1) have "Man Socrates \<longrightarrow> Mortal Socrates" by (erule_tac x = "Socrates" in allE)
    ultimately
    show "Mortal Socrates" by - (erule impE, assumption)
  qed
qed 

(*
lemma 
  assumes "\<forall>x. Man x \<longrightarrow> Mortal x"
  assumes "\<forall>x. Greek x \<longrightarrow> Man x" 
  shows "\<forall>x. Greek x \<longrightarrow> Mortal x"
proof -
  fix Socrates
  assume "Greek Socrates"
  from \<open>\<forall>x. Greek x \<longrightarrow> Man x\<close> have "Greek Socrates \<longrightarrow> Man Socrates" by auto 
  from assms(1) have "Man Socrates \<longrightarrow> Mortal Socrates" by auto 
  show "Mortal Socrates" by auto
qed
*)

lemma "(A \<and> B \<longrightarrow> C ) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C ))"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply (rule conjI)
    apply assumption +
  done 

lemma "(A \<longrightarrow> (B \<longrightarrow> C )) \<longrightarrow> (A \<and> B \<longrightarrow> C )"
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule impE)
   apply (erule conjE)
   apply assumption +
  done 

lemma "\<not> A \<and> \<not> B \<longrightarrow> \<not> (A \<or> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE) back
  apply assumption 
  done 

lemma "\<not> A \<and> \<not> B \<longrightarrow> \<not> (A \<or> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule disjE)
   apply (erule conjE)
   apply (erule notE)
   apply assumption 
  apply (erule conjE)
  apply (erule notE) back 
  apply assumption
  done 

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back 
   apply (rule notI)
   apply (erule impE)
    apply assumption 
   apply (erule notE)
   apply assumption 
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  apply (rule impI)
  apply (rule iffI)
   apply (erule conjE) + 
   apply (erule impE) back  back 
    apply assumption 
   apply (erule disjE)
    apply assumption 
   apply (erule impE) back 
    apply assumption 
   apply (erule conjE)
   apply assumption
  apply (erule conjE) + 
  apply (erule impE) 
   apply assumption 
  apply (erule impE) 
   apply assumption 
  apply (erule conjE)
  apply assumption 
  done 


lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  apply (rule impI)+
  apply (rule conjI)
   apply (erule conjE)
   apply (erule impE)
    apply assumption + 
  apply (erule conjE)
  apply (erule impE) 
   apply assumption 
  apply (erule impE)
   apply assumption +
  done 

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  apply (rule impI)+
  apply (erule impE)
   apply assumption 
  apply (erule impE)
   apply assumption +
  done 

lemma "\<not> (P \<and> \<not>P)"
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done 

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B) \<or> (A \<and> C )"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption +
  apply (rule disjI2)
  apply (rule conjI)
   apply assumption +
  done 

lemma "\<not> (A \<and> B) \<longrightarrow> (A \<longrightarrow> \<not> B)"
  apply (rule impI)+
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI)
   apply assumption +
  done 

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule notI)
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma 
  fixes x y:: nat
  shows "(x + y)^2 = x^2 + 2*x*y + y^2"
proof -
  have "(x + y)^2 = (x + y) * (x + y)" by (simp add: power2_eq_square)
  also have "... = x*(x + y) + y * (x + y)" by (simp add: add_mult_distrib)  
  also have "... = (x*x + x*y) + y * (x + y)" by (simp add: add_mult_distrib2)
  also have "... = (x*x + x*y) + (y*x + y*y)" by (simp add: add_mult_distrib2)
  also have "... = x*x + (x*y + y*x) + y*y" by simp 
  also have "... = x^2 + (x*y + y*x) + y*y" by (simp add: power2_eq_square)
  also have "... = x^2 + (x*y + x*y) + y*y" by simp 
  also have "... = x^2 + x*y + x*y + y*y" by simp 
  also have "... = x^2 + 2*x*y + y*y" by simp 
  also have "... = x^2 + 2*x*y + y^2" by (simp add: power2_eq_square)
  finally show ?thesis by simp 
qed

lemma 
  fixes x y z:: nat
  shows "(x + y) * (x + z) = x^2 + x * (y + z) + y*z"
proof -
  have "(x + y) * (x + z) = x * (x + z) + y * (x + z)" by (simp add: add_mult_distrib)
  also have "... = (x*x + x*z) + y*(x + z)" by (simp add: add_mult_distrib2)
  also have "... = (x*x + x*z) + (y*x + y*z)" by (simp add: add_mult_distrib2)
  also have "... = x*x + x*z + (y*x + y*z)" by simp
  also have "... = x^2 + x*z + (y*x + y*z)" by (simp add: power2_eq_square)
  also have "... = x^2 + (x*z + y*x) + y*z" by simp 
  also have "... = x^2 + (x*z + x*y) + y*z" by simp 
  also have "... = x^2 + x * (z + y) + y*z" by (simp add: add_mult_distrib2)
  also have "... = x^2 + x * (y + z) + y*z" by simp 
  finally show ?thesis by simp 
qed

primrec suma_n :: "nat \<Rightarrow> nat" where 
  "suma_n 0 = 0"
| "suma_n (Suc n) = (Suc n) + suma_n n" 

value "suma_n 5"

lemma 
  fixes n :: nat
  shows"suma_n n = n*(n + 1) div 2"
  by (induction n) auto

lemma
  fixes n:: nat
  shows "suma_n n = n * (n + 1) div 2"
proof (induction n)
  case 0
  then show ?case by simp 

next
  case (Suc n)
  note IH = this 

  have "suma_n (Suc n) = (Suc n) + suma_n n" by simp 
  also have "... = (Suc n) + n * (n + 1) div 2" using IH by simp 
  also have "... = (n + 1) + n * (n + 1) div 2" by simp 
  also have "... = 2 * (n + 1) div 2 + n * (n + 1) div 2" by simp 
  also have "... = (2 * (n + 1) + n * (n + 1)) div 2" by simp 
  also have "... = ((n + 1) * (n + 2)) div 2" by simp 
  also have "... = ((Suc n) * (Suc (n + 1))) div 2" by simp
  finally show ?case by simp 
qed

type_synonym mat2 = "nat \<times> nat \<times> nat \<times> nat" 

term "(1,0,0,1)::mat2"

definition eye:: "mat2" where 
  "eye \<equiv> (1, 0, 0, 1)"

fun mat_mul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" where 
  "mat_mul (a1, b1, c1, d1) (a2, b2, c2, d2) = (a1*a2+b1*c2, a1*b2+b1*d2, c1*a2+d1*c2, c1*b2+d1*d2)"

value "mat_mul (1,2,3,4) (1, 0, 0, 1)"

fun mat_pow :: "mat2 \<Rightarrow> nat \<Rightarrow> mat2" where 
  "mat_pow M 0 = eye"
| "mat_pow M (Suc n) = mat_mul (mat_pow M n) M" 

value "mat_pow (1,1,0,1) 3"

lemma 
  fixes n:: nat 
  shows "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
  by (induction n) (auto simp add: eye_def)

lemma 
  fixes n :: nat 
  shows "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
proof (induction n)
  case 0 
  then show ?case 
    by (auto simp add: eye_def)

next
  case (Suc n)
  note IH = this 

  have "mat_pow (1, 1, 0, 1) (Suc n) = mat_mul (mat_pow (1, 1, 0, 1) n) (1, 1, 0, 1)" by simp 
  also have "... = mat_mul (1, n, 0, 1) (1, 1, 0, 1)" using IH by simp 
  also have "... = (1, n+1, 0, 1)" by simp 
  also have "... = (1, Suc n, 0, 1)" by simp 
  finally show ?case by simp 
qed


type_synonym mat22 = "int \<times> int \<times> int \<times> int"

fun mat_mul1 :: "mat22 \<Rightarrow> mat22 \<Rightarrow> mat22" where 
  "mat_mul1 (a1, b1, c1, d1) (a2, b2, c2, d2) = (a1*a2+b1*c2, a1*b2+b1*d2, c1*a2+d1*c2, c1*b2+d1*d2)"


definition eye1 :: "mat22" where 
  "eye1 \<equiv> (1, 0, 0, 1)"

term "(1, 1, 1, 1)::mat22"

fun mat_pow1 :: "mat22 \<Rightarrow> nat \<Rightarrow> mat22" where 
  "mat_pow1 M 0 = eye1"
| "mat_pow1 M (Suc n) = mat_mul1 (mat_pow1 M n) M" 

value "mat_pow1 (1, -1, 0, 2) 3"

lemma "mat_pow1 (1, -1, 0, 2) n = (1, 1 - 2^n, 0, 2^n)"
  by (induction n) (auto simp add: eye1_def) 

lemma 
  fixes n:: nat 
  shows "mat_pow1 (1, -1, 0, 2) n = (1, 1 - 2^n, 0, 2^n)"
proof (induction n)
  case 0
  then show ?case by (auto simp add: eye1_def)

next
  case (Suc n)
  note IH = this 

  have "mat_pow1 (1, -1, 0, 2) (Suc n) = mat_mul1 (mat_pow1 (1, -1, 0, 2) n) (1, -1, 0, 2)" by simp 
  also have "... = mat_mul1 (1, 1 - 2^n, 0, 2^n) (1, -1, 0, 2)" using IH by simp 
  also have "... = (1, 1 - 2^(n + 1), 0, 2^(n + 1))" by simp 
  also have "... = (1, 1 - 2^(Suc n), 0, 2^(Suc n))" by simp 
  finally show ?case by simp 
qed

lemma 
  fixes n :: nat 
  shows "3 dvd ((5::nat)^(n) + 2^(n+1))"
proof (induction n)
  case 0
  then show ?case by (simp add: numeral_3_eq_3)
next
  case (Suc n)

  then obtain k::nat where IH: "(5::nat)^n + 2^(n + 1) = 3*k" 

    have "(5::nat)^(Suc n) + 2^(Suc n + 1) = 5^(n + 1) + 2^(n + 2)" by auto 
    also have "... = 5*5^n + 2 * 2^(n + 1)" by auto 
    also have "... = 5 * (5^n + 2^(n + 1)) - 5 * 2^(n + 1) + 2 * 2^(n+1)" by auto 
    also have "... = 5 * 3*k - 3 * 2^(n + 1)" using IH by auto 
    also have "... = 3 * (5 * k - 2^(n + 1))" by auto 
    finally  show ?case by (metis Suc_eq_plus1 \<open>3 * k = 5 * 5 ^ n + 2 * 2 ^ (n + 1)\<close> dvd_def power_Suc)
qed

qed


end 