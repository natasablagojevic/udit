theory Cas6
  imports Main

begin

lemma
  assumes "\<exists>x. P x" and "\<forall>x. P x \<longrightarrow> Q x"
  shows "\<exists>x. Q x"
proof-
  from assms(1) obtain x where "P x" by -(erule exE)
  moreover 
  from assms(2) have "P x \<longrightarrow> Q x" by (erule_tac x="x" in allE)
  ultimately
  have "Q x" by -(erule impE, assumption)
  then show "\<exists>x. Q x" by (rule_tac x="x" in exI)
qed

(*
lemma 
  assumes "\<forall>c. Man c \<longrightarrow> Mortal c" and "\<forall>g. Greek g \<longrightarrow> Man g"
  shows "\<forall>a. Greek a \<longrightarrow> Mortal a"
proof
 (* fix Socrates 
  assume "Greek Socrates"
  moreover
  from assms(2) have "Greek Socrates \<longrightarrow> Man Socrates" 
    by (erule_tac x="Socrates" in allE)
  ultimately
  have "Man Socrates" by -(erule impE, assumption)
  moreover
  from assms(1) have "Man Socrates \<longrightarrow> Mortal Socrates"
    by (erule_tac x="Socrates" in allE)
  ultimately
  show "Mortal Socrates" by -(erule impE, assumption)
*)
  fix Socrates
  show "Greek Socrates \<longrightarrow> Mortal Socrates"
  proof
    assume "Greek Socrates"
    from this and assms(2) have "Man Socrates" by auto 
    from this and assms(1) have "Mortal Socrates" by auto 
  qed
qed
*)

lemma 
  assumes "\<forall>c. covek c \<longrightarrow> smrtan c"
  assumes "\<forall>g. grk g \<longrightarrow> covek g"
  shows "\<forall>a. grk a \<longrightarrow> smrtan a"
proof
  fix Jorgus 
  show "grk Jorgus \<longrightarrow> smrtan Jorgus"
  proof
    assume "grk Jorgus"
    moreover 
    from assms(2) have "grk Jorgus \<longrightarrow> covek Jorgus" by auto 
    ultimately
    have "covek Jorgus" by auto
    moreover
    from assms(1) have "covek Jorgus \<longrightarrow> smrtan Jorgus" by auto
    ultimately
    show "smrtan Jorgus" by auto 
  qed
qed


lemma "(\<forall>a. P a \<longrightarrow> Q a) \<and> (\<forall>b. P b) \<longrightarrow> (\<forall>x. Q x)"
  apply (rule impI)
  apply (rule allI)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)+
  apply (erule impE)
   apply assumption+
  done 

lemma 
  assumes "\<forall>a. P a \<longrightarrow> Q a"
  assumes "\<forall>b. P b"
  shows "\<forall>x. Q x"
proof
  fix x
  show "Q x"
  proof- 
    from assms(2) have "P x" by auto 
    from assms(1) have "P x \<longrightarrow> Q x" by auto
    from this \<open>P x\<close> show "Q x" by auto
  qed
qed


lemma "(\<exists>x. A x \<or> B x) \<longrightarrow> (\<exists>x. A x) \<or> (\<exists>x. B x)"
  apply (rule impI)
  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule_tac x="x" in exI)
   apply assumption
  apply (rule disjI2)
  apply (rule_tac x="x" in exI)
  apply assumption
  done 


lemma 
  assumes "\<exists>x. A x \<or> B x"
  shows "(\<exists>x. A x) \<or> (\<exists>x. B x)"
proof-
  from assms obtain x where "A x \<or> B x" by auto 
  from this show "(\<exists>x. A x) \<or> (\<exists>x. B x)"
  proof
    assume "A x"
    from this show "(\<exists>x. A x) \<or> (\<exists>x. B x)" by auto
  next 
    assume "B x"
    show "(\<exists>x. A x) \<or> (\<exists>x. B x)"
    proof-
      from \<open>B x\<close> have "\<exists>x. B x" by auto 
      from this show "(\<exists>x. A x) \<or> (\<exists>x. B x)" by auto 
    qed
  qed  
qed


lemma "(\<forall> x. A x \<longrightarrow> \<not> B x) \<longrightarrow> \<not> (\<exists> x. A x \<and> B x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption 
  done 

lemma 
  assumes "\<forall> x. A x \<longrightarrow> \<not> B x"
  shows " \<not> (\<exists> x. A x \<and> B x)"
proof
  assume "\<exists>x. A x \<and> B x"
  from this obtain x where "A x \<and> B x" by auto 
  from this have "A x" "B x" by auto 
  from this have "\<not> B x" using assms by auto 
  from this \<open>B x\<close> show "False" by auto
qed

(*
Ako za svaki broj koji nije paran vazi da je neparan; 
i ako za svaki neparan broj vazi da nije paran; 
pokazati da onda za svaki broj vazi da nije istovremeno i paran i neparan

paran(x) = x je paran 
neparan(x) =  x je neparan 

\<forall>x. \<not> paran x \<longrightarrow> neparan x
\<forall>x. neparan x \<longrightarrow> \<not> paran x
\<forall>x.\<not> ( paran x \<and> neparan x)

*)

lemma "(\<forall>x. \<not> paran x \<longrightarrow> neparan x) \<and> (\<forall>x. neparan x \<longrightarrow> \<not> paran x) \<longrightarrow> (\<forall>x.\<not> ( paran x \<and> neparan x))"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule conjE)+
  apply (erule_tac x="x" in allE)+
  apply (erule impE)+
    apply assumption + 
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma 
  assumes "\<forall>x. \<not> paran x \<longrightarrow> neparan x"
  assumes "\<forall>x. neparan x \<longrightarrow> \<not> paran x"
  shows "\<forall>x.\<not> ( paran x \<and> neparan x)"
proof
  fix x 
  show "\<not> ( paran x \<and> neparan x)"
  proof
    assume "paran x \<and> neparan x"
    from this have "paran x" "neparan x" by auto 
    from this assms(2) have "\<not> paran x" by auto 
    from this \<open>paran x\<close> show "False" by auto
  qed
qed

(*
Ako za svaki broj koji nije paran vazi da je neparan; 
i ako za svaki neparan broj vazi da nije paran; 
pokazati da onda za svaki broj vazi da je ili paran ili neparan

\<forall>x. \<not> paran x \<longrightarrow> neparan x
\<forall>x. neparan x \<longrightarrow> \<not> paran x 
\<longrightarrow> \<forall>x. paran x \<or> neparan x

*)

lemma "(\<forall>x. \<not> paran x \<longrightarrow> neparan x) \<and> (\<forall>x. neparan x \<longrightarrow> \<not> paran x) \<longrightarrow> (\<forall>x. paran x \<or> neparan x)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)+
  apply (rule ccontr)
  apply (erule impE)
  apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
  apply (assumption)
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply (rule disjI2)
  apply assumption 
  done 

lemma 
  assumes "\<forall>x. \<not> paran x \<longrightarrow> neparan x"
  assumes "\<forall>x. neparan x \<longrightarrow> \<not> paran x"
  shows "\<forall>x. paran x \<or> neparan x"
proof
  fix x
  have "paran x \<or> \<not> paran x" by auto 
  from this show "paran x \<or> neparan x"
  proof
    assume "paran x"
    from this show "paran x \<or> neparan x" by auto

  next 
    assume "\<not> paran x"
    from this have "neparan x" using assms(1) by auto 
    from this show "paran x \<or> neparan x" by auto 
  qed
qed



(*

Ako svaki konj ima potkoice;
i ako ne postoji covek koji ima potkovice;
i ako znamo da postoji makar jedan covek ;
dokazati da postoji covek koji nije konj;

\<forall>x. konj x \<longrightarrow> potkovice x 
\<nexists>x. covek x \<and> potkovice x 
\<exists>x. covek x 
\<longrightarrow> \<exists>x. covek x \<and> \<not> konj x

*)

lemma "(\<forall>x. konj x \<longrightarrow> potkovice x) \<and> (\<nexists>x. covek x \<and> potkovice x) \<and> (\<exists>x. covek x) \<longrightarrow> (\<exists>x. covek x \<and> \<not> konj x)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption
  apply (rule notI)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption+
  done 

lemma 
  assumes "\<forall>x. konj x \<longrightarrow> potkovice x"
  assumes "\<not>(\<exists>x. covek x \<and> potkovice x)"
  assumes "\<exists>x. covek x"
  shows "\<exists>x. covek x \<and> \<not> konj x"
proof-
  from assms(3) obtain x where "covek x" by auto 
  have "konj x \<or> \<not> konj x" by auto 
  from this have "covek x \<and> \<not> konj x" 
  proof
    assume "konj x"
    show "covek x \<and> \<not> konj x" 
    proof
      from \<open>covek x\<close> show "covek x" by auto 
    next 
      show "\<not> konj x"
      proof
        assume "konj x"
        from this assms(1) have "potkovice x" by auto 
        from \<open>covek x\<close> this have "\<exists>x. covek x \<and> potkovice x" by auto 
        from this assms(2) show "False" by auto 
      qed
    qed
  next 
    assume "\<not> konj x"
    from this and \<open>covek x\<close>
    show "covek x \<and> \<not> konj x" by auto 
  qed
  from this show "\<exists>x. covek x \<and> \<not> konj x" by auto
qed

lemma
  assumes "\<forall>x. kvadrat x \<longrightarrow> romb x"
  assumes "\<forall>x. kvadrat x \<longrightarrow> pravougaonik x"
  assumes "\<exists>x. kvadrat x"
  shows "\<exists>x. romb x \<and> pravougaonik x"
proof-
  from assms(3) obtain x where "kvadrat x" by auto
  from this assms(2) have "pravougaonik x" by auto
  from assms(1) \<open>kvadrat x\<close> have "romb x" by auto 
  from this \<open>pravougaonik x\<close> show "\<exists>x. romb x \<and>pravougaonik x" by auto
qed









end