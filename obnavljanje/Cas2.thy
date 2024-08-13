theory Cas2
  imports Main 

begin 

(*
Ako ”šta leti to ima krila i lagano je” i ”šta pliva, to nema krila”, onda ”šta pliva, to ne leti”

leti(x) = x leti 
krila(x) = x ima krila 
lagano(x) = x je lagano 
pliva(x) = x pliva 

\<forall>x. leti x \<longrightarrow> krila x \<and> lagano x
\<forall>x. pliva x \<longrightarrow> \<not> (krila x)
\<forall>x. pliva x \<longrightarrow> \<not> (leti x)

*)

lemma "(\<forall>x. leti x \<longrightarrow> krila x \<and> lagano x) \<and> (\<forall>x. pliva x \<longrightarrow> \<not> (krila x)) \<longrightarrow> (\<forall>x. pliva x \<longrightarrow> \<not> (leti x))"
  by auto 


(*
 Ako postoji cipela koja u svakom trenutku odgovara svakoj nozi,
\<exists>c. \<forall>t. \<forall>n. P c t n

 onda za svaku nogu postoji cipela koja joj u nekom trenutku odgovara 
\<forall>n. \<exists>c. \<exists>t. P c t n

i za svaku nogu postoji trenutak takav da postoji cipela koja joj u tom trenutku odgovara.
\<forall>n. \<exists>t. \<exists>c. P c t n


c - cipela 
t - trenutak 
n - noga 

P - predikat 

*)

lemma "(\<exists>c. \<forall>t. \<forall>n. P c t n) \<longrightarrow>  (\<forall>n. \<exists>c. \<exists>t. P c t n) \<and> (\<forall>n. \<exists>t. \<exists>c. P c t n)"
  by auto

(*

P: Andrija voli da pleše.
P1: Svako ko je srećan voli da peva.
P2: Svako ko voli da peva, voli da pleše.
P3: Andrija je srećan.

plese(x) = x voli da plese 
srecan(x) = x je srecan 
peva(x) = x peva

P1: \<forall>x. srecan x \<longrightarrow> peva x 
P2: \<forall>x. peva x \<longrightarrow> plese x 
P3: srecan Andrija 

P: plese Andrija


*)

lemma "(\<forall>x. srecan x \<longrightarrow> peva x) \<and> (\<forall>x. peva x \<longrightarrow> plese x) \<and> (srecan Andrija) \<longrightarrow> (plese Andrija)"
  by auto 

(*
P: Svako dete voli da se igra.
P1: Svaki dečak voli da se igra.
P2: Svaka devojčica voli da se igra.
P3: Dete je dečak ili je devojčica.

decak(x) = x je dacak 
devojcica(x) = x je devojcica 
igra(x) = x voli da se igra 

P1: \<forall>x. decak x \<longrightarrow> igra x 
P2: \<forall>x. devojcica x \<longrightarrow> igra x 
P3: \<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x 

P: \<forall>x. dete x \<longrightarrow> igra x
*)

lemma "(\<forall>x. decak x \<longrightarrow> igra x) \<and> (\<forall>x. devojcica x \<longrightarrow> igra x) \<and> (\<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x) \<longrightarrow> (\<forall>x. dete x \<longrightarrow> igra x)"
  by auto

(*
Svaka dva brata imaju zajedničkog roditelja.
- Roditelj je stariji od deteta.
- Postoje braća.
- Nijedna osoba nije starija od druge

brat(x, y) = x i y su braca 
roditelj(x, y) = x je roditelj od y 
straija(x, y) = x je stariji od y 

\<forall>x. \<forall>y.\<exists>z.  brat x y \<longrightarrow> roditelj z x \<and> roditelj z y
\<forall>x. \<forall>y. roditelj x y \<longrightarrow> stariji x y
\<exists>x. \<exists>y. brat x y 
\<not>(\<exists>x. \<exists>y. stariji x y)

*)

lemma "(\<forall>x. \<forall> y.\<exists> z. brat x y \<longrightarrow>  roditelj z x \<and> roditelj z y) \<and> (\<forall>x. \<forall>y. roditelj x y \<longrightarrow> stariji x y) \<and> (\<exists>x.\<exists>y. brat x y) \<and> (\<not>(\<exists>x. \<exists>y. stariji x y)) \<longrightarrow> False"
  by auto


(*

All men are mortal. (MaP)
All Greeks are men. (SaM)
— All Greeks are mortal. (SaP)

men(x) = x are men
mortal(x) = x is mortal 
greeks(x) = x are greeks

\<forall>x. men x \<longrightarrow> mortal x 
\<forall>x. greeks x \<longrightarrow> men x 
\<forall>x. greeks x \<longrightarrow> mortal x

*)

lemma "(\<forall>x. men x \<longrightarrow> mortal x) \<and> (\<forall>x. greeks x \<longrightarrow> men x) \<longrightarrow> (\<forall>x. greeks x \<longrightarrow> mortal x)"
  by auto 

(*
No reptiles have fur. (MeP)
All snakes are reptiles. (SaM)
— No snakes have fur.

\<not>(\<exists>x. reptiles x \<and> fur x)
\<forall>x. snake x \<longrightarrow> reptiles x
\<not>(\<exists>x. snake x \<and> fur x)

*)

lemma "(\<not>(\<exists>x. reptiles x \<and> fur x)) \<and> (\<forall>x. snake x \<longrightarrow> reptiles x) \<longrightarrow> (\<not>(\<exists>x. snake x \<and> fur x))"
  by auto 

(*
No homework is fun. (MeP)
Some reading is homework. (SiM)
— Some reading is not fun. (SoP)

\<nexists>x. homework x \<and> fun x)
\<exists>x. reading x \<and> homework x 
\<exists>x. reading x \<and> (\<not> fun x)  

*)

lemma "(\<nexists>x. homework x \<and> fun x) \<and> (\<exists>x. reading x \<and> homework x) \<longrightarrow> (\<exists>x. reading x \<and> (\<not> fun x))"
  by auto

(*
Some cats are not pets. (MoP)
All cats are mammals. (MaS)
— Some mammals are not pets

\<exists>x. cats x \<and> (\<not> pets x)
\<forall>x. cats x \<longrightarrow> mammals x 
\<exists>x. mammals x \<and> (\<not> pets x)

*)

lemma "(\<exists>x. cats x \<and> (\<not> pets x)) \<and> (\<forall>x. cats x \<longrightarrow> mammals x) \<longrightarrow> (\<exists>x. mammals x \<and> (\<not> pets x))"
  by auto


(*
All men are mortal. (MaP)
All Greeks are men. (SaM)
— Some Greeks are mortal

\<forall>x. men x \<longrightarrow> mortal x 
\<forall>x. greeks x \<longrightarrow> men x 
\<exists>x. greeks x \<and> mortal x 

*)

lemma Barbari: "(\<forall>x. men x \<longrightarrow> mortal x) \<and> (\<forall>x. greeks x \<longrightarrow> men x) \<and> (\<exists>x. greeks x) \<longrightarrow> (\<exists>x. greeks x \<and> mortal x)"
  by auto

(*

No reptiles have fur. (MeP)
All snakes are reptiles. (SaM)
— Some snakes have no fur. (SoP)

\<nexists>x. reptiles x \<and> fur x 
\<forall>x. snakes x \<longrightarrow> reptiles x 
\<exists>x. snakes x \<and> (\<not> fur x)

*)

lemma "(\<nexists>x. reptiles x \<and> fur x) \<and> (\<forall>x. snakes x \<longrightarrow> reptiles x) \<and> (\<exists>x. snakes x) \<longrightarrow> (\<exists>x. snakes x \<and> (\<not> fur x))"
  by auto


(*
All horses have hooves. (PaM)
No humans have hooves. (SeM)
— Some humans are not horses. (SoP)

\<forall>x. horses x \<longrightarrow> hooves x 
\<not>(\<exists>x. humans x \<and> hooves x)
\<exists>x. humans x \<and> (\<not> horses x)

*)

lemma "(\<forall>x. horses x \<longrightarrow> hooves x) \<and> (\<not>(\<exists>x. humans x \<and> hooves x)) \<and> (\<exists>x. humans x) \<longrightarrow> (\<exists>x. humans x \<and> (\<not> horses x))"
  by auto

(*----------------------------------------------------------------------------------------------------------------------------*)

(*
1. svaka osoba ce odgovoriti potvrdno na pitanje: Da li si ti vitez?
*)

lemma 
  assumes "kaze  \<longleftrightarrow> (kaze \<longleftrightarrow> ansK)"
  shows "ansK"
  using assms
  by auto


lemma 
  assumes "(kA \<longleftrightarrow> (kA \<longleftrightarrow> ansA))" and "kB \<longleftrightarrow> \<not> ansA" and "kC \<longleftrightarrow> \<not> kB"
  shows "kC"   (* C je vitez *)
  using assms 
  by auto 

definition exactlyTwo:: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
  where "exactlyTwo a b c \<longleftrightarrow> ((a \<and> b) \<or> (a \<and> c) \<or> (b \<and> c)) \<and> \<not>(a \<and> b \<and> c)"

lemma 
  assumes "kA \<longleftrightarrow> ansA" and "kB \<longleftrightarrow> (exactlyTwo (\<not>kA) (\<not>kB) (\<not>kC) \<longleftrightarrow> ansA)" and "kC \<longleftrightarrow> \<not> kB"
  shows "kC"      (* C je vitez *)
  using assms
  unfolding exactlyTwo_def 
  by auto

(* Ako B kaze da je A rekao da su tacno 2 viteza \<longrightarrow> C je podanik*)


end