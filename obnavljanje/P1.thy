theory P1
  imports Main

begin

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption+
  done 

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done 

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply (rule impI)+
  apply (erule impE)
   apply (rule conjI)
    apply assumption+
  done 

lemma "\<not> (A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
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

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  apply (rule impI)+
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (rule conjI)
   apply assumption
  apply (erule impE)
   apply assumption+
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
   apply assumption+
  done 

lemma "\<not> (P \<and> \<not>P)"
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done 

lemma "A \<and> (B \<or> C) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption+
  apply (rule disjI2)
  apply (rule conjI)
   apply assumption+
  done 

lemma "\<not> (A \<and> B) \<longrightarrow> (A \<longrightarrow> \<not>B)"
  apply (rule impI)+
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI)
   apply assumption+
  done

lemma "(A \<longrightarrow> C) \<and> (B \<longrightarrow> \<not> C) \<longrightarrow> \<not> (A \<and> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<and> B) \<longrightarrow> ((A \<longrightarrow> C) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C))"
  apply (rule impI)+
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
  apply assumption
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE)
   apply (rule ccontr)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(A \<longleftrightarrow> B) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B)"
  apply (rule impI)
  apply (rule iffI)
   apply (erule iffE)
   apply (rule notI)
   apply (erule impE)+
     apply assumption+
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  apply (rule impI)
  apply (rule iffI)
   apply (erule conjE)+
   apply (erule impE) back back 
    apply assumption
   apply (erule disjE)
    apply assumption
   apply (erule impE)back
    apply assumption 
   apply (erule conjE)
   apply assumption
  apply (erule conjE)+
  apply (erule impE)
  apply assumption
  apply (erule impE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done 


lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
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


lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply assumption
  done 

lemma "(\<not> B \<longrightarrow> \<not> A) \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI)+
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)back
  apply assumption
  done 

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> A \<or> B)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption 
  apply (erule notE)
  apply (rule disjI2)
  apply assumption 
  done 

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule ccontr)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption 
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule ccontr)
   apply (erule impE)
    apply assumption
  apply (erule notE)
   apply assumption 
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE) 
  apply (rule classical)
  apply (rule impI)
   apply (erule notE) 
   apply assumption 
  apply (erule notE)
  apply assumption
  done 


lemma 
  assumes "(P \<longrightarrow> Q) \<longrightarrow> P"
  shows "P"
proof (rule ccontr)
  assume "\<not>P" 
  have "P \<longrightarrow> Q"
  proof
    assume "P"
    from this \<open>\<not>P\<close> show "Q" by auto
  qed
  from this assms have "P" by auto 
  from this \<open>\<not> P\<close> show "False" by auto
qed

definition "reflexive R \<longleftrightarrow> (\<forall>x. R x x)"
definition "transitive R \<longleftrightarrow> (\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z)"
definition "symetric R \<longleftrightarrow> (\<forall>x y. R x y \<longleftrightarrow> R y x)"

lemma "symetric R \<and> transitive R \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> reflexive R"
  unfolding symetric_def transitive_def reflexive_def
  apply (rule impI)
  apply (erule conjE)+
  apply (rule allI)
  apply (erule_tac x="x" in allE) back back 
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
  apply (rule conjI)
    apply assumption 
  apply (erule iffE)
   apply (erule impE) 
    apply assumption+
  done 


lemma "(nA \<longleftrightarrow> bA \<or> bB) \<and> (nB \<longleftrightarrow> \<not> bA) \<and> ((nA \<and> nB) \<or> (\<not> nA \<and> \<not> nB)) \<longrightarrow> \<not> bA \<and> bB"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule disjE)
  apply (erule conjE)
  apply (erule iffE)
  apply (erule impE)
    apply assumption 
   apply (erule iffE)
  apply (erule impE)
    apply assumption 
   apply (erule impE)
  apply assumption 
   apply (rule conjI)
  apply assumption 
  apply (erule impE)
    apply assumption 
   apply (rule ccontr)
  apply (erule disjE)
    apply (erule notE)
    apply assumption 
   apply (erule notE) back 
   apply assumption 
  apply (erule conjE)
  apply (erule iffE)+
  apply (erule impE)
   apply (erule impE) back
    apply (rule ccontr)
    apply (erule impE) back 
     apply (rule notI)
     apply (erule notE) back back 
  sorry 


lemma 
  assumes "\<exists>x. P x"
  assumes "\<forall>x. P x \<longrightarrow> Q x"
  shows "\<exists>x. Q x"
proof-
  from assms(1) obtain x where "P x" by auto
  from assms(2) have "P x \<longrightarrow> Q x" by auto 
  from this \<open>P x\<close> have "Q x" by auto 
  from this show "\<exists>x. Q x" by auto 
qed


lemma 
  assumes "\<forall>x. covek x \<longrightarrow> smrtan x"
  assumes "\<forall>x. grk x \<longrightarrow> covek x"
  shows "\<forall>x. grk x \<longrightarrow> smrtan x"
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



lemma 
  assumes "\<forall>x. P x \<longrightarrow> Q x"
  assumes "\<forall>x. P x"
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


lemma 
  assumes "\<exists>x. A x \<or> B x"
  shows "(\<exists>x. A x) \<or> (\<exists>x. B x)"
proof-
  from assms obtain x where "A x \<or> B x" by auto 
  from this show "(\<exists>x. A x) \<or> (\<exists>x. B x)"
  proof
    assume "A x" 
    from \<open>A x\<close> have "\<exists>x. A x" by auto 
    from this show "(\<exists>x. A x) \<or> (\<exists>x. B x)" by auto
  next
    assume "B x"
    from \<open>B x\<close> have "\<exists>x. B x" by auto
    from this show "(\<exists>x. A x) \<or> (\<exists>x. B x)" by auto
  qed
qed

lemma 
  assumes "\<forall>x. A x \<longrightarrow> \<not> B x"
  shows "\<not> (\<exists>x. A x \<and> B x)"
proof
  assume "\<exists>x. A x \<and> B x"
  from this obtain x where "A x \<and> B x" by auto 
  from this have "A x" "B x" by auto
  from this have "\<not> B x" using assms by auto
  from this \<open>B x\<close> show "False" by auto
qed


lemma 
  assumes "\<forall>x. \<not> paran x \<longrightarrow> neparan x"
  assumes "\<forall>x. neparan x \<longrightarrow> \<not> paran x"
  shows "\<forall>x. \<not> (paran x \<and> neparan x)"
proof
  fix x
  show " \<not> (paran x \<and> neparan x)"
  proof
    assume "paran x \<and> neparan x" (*Show FALSE*)
    from this have "paran x" "neparan x" by auto 
    from this have "\<not> paran x" using assms(2)  by auto 
    from this \<open>paran x\<close> show False by auto
  qed
qed

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

lemma 
  assumes "\<forall>x. Man x \<longrightarrow> Mortal x"
  assumes "\<forall>x. Greek x \<longrightarrow> Man x"
  shows "\<forall>x. Greek x \<longrightarrow> Mortal x"
proof
  fix x
  show "Greek x \<longrightarrow> Mortal x"
  proof
    assume "Greek x"
    moreover
    from assms(2) have "Greek x \<longrightarrow> Man x" by auto
    ultimately
    have "Man x" by auto
    moreover
    from assms(1) have "Man x \<longrightarrow> Mortal x" by auto 
    ultimately
    show "Mortal x" by auto
  qed
qed


lemma 
  assumes "\<forall>x. konj x \<longrightarrow> potkovica x"
  assumes "\<not>(\<exists>x. covek x \<and> potkovica x)"
  assumes "\<exists>x. covek x"
  shows "\<exists>x. covek x \<and> \<not> konj x"
proof-
  from assms(3) obtain x where "covek x" by auto 
  have "konj x \<or> \<not> konj x" by auto
  then show "\<exists>x. covek x \<and> \<not> konj x" 
  proof
    assume "konj x"
    moreover
    from this and assms(1) have "konj x \<longrightarrow> potkovica x" by auto
    ultimately
    have "potkovica x" by auto
    with \<open>covek x\<close> have "covek x \<and> potkovica x" by auto 
    then have "\<exists>x. covek x \<and> potkovica x" by auto
    with assms(2) have False by auto
    then show "\<exists>x. covek x \<and> \<not> konj x" by auto
  next 
    assume "\<not> konj x"
    with \<open>covek x\<close> have "covek x \<and> \<not> konj x" by auto
    then show "\<exists>x. covek x \<and> \<not> konj x" by auto
  qed
qed








end 