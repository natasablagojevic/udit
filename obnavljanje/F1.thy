theory F1
  imports Main

begin 

lemma "P \<and> Q \<longrightarrow> P \<or> Q"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done

lemma "P \<and> Q \<longrightarrow> P \<or> Q"
proof
  assume "P \<and> Q"
  then have "P" "Q" by auto
  from \<open>Q\<close> show "P \<or> Q" by auto
qed

lemma "\<not>(A \<or> B) \<longleftrightarrow> \<not> A \<and> \<not> B"
proof
  assume *:"\<not> (A \<or> B)"
  show "\<not> A \<and> \<not> B"
  proof
    show "\<not> A"
    proof
      assume "A"
      from this have "A \<or> B" by auto 
      from \<open>A \<or> B\<close> \<open>\<not>(A \<or> B)\<close> show False by auto 
    qed
  next
    show "\<not> B"
    proof
      assume "B"
      from this have "A \<or> B" by auto
      from \<open>A \<or> B\<close> \<open>\<not>(A \<or> B)\<close> show False by auto
    qed
  qed

next 
  assume "\<not> A \<and> \<not> B"
  then have "\<not> A" "\<not> B" by auto
  show "\<not> (A \<or> B)"
  proof
    assume "A \<or> B"
    then show False 
    proof
      assume "A"
      with \<open>\<not> A\<close> show False by auto       
    next
      assume "B"
      with \<open>\<not>B\<close> show False by auto
    qed
  qed
qed

lemma lemma "\<not>(A \<and> B) \<longleftrightarrow> \<not> A \<or> \<not> B" (is "?l \<longleftrightarrow> ?d")
proof
  assume "\<not> (A \<and> B)"
  show " \<not> A \<or> \<not> B"
  proof (rule ccontr)
    assume "\<not> (\<not> A \<or> \<not> B)"
    have "A \<and> B" 
    proof
      show "A"
      proof (rule ccontr)
        assume "\<not>A"
        then have "\<not> A \<or> \<not> B" by auto
        from this \<open>\<not>(\<not> A \<or> \<not> B)\<close>  show False by auto
      qed
    next
      show "B"
      proof (rule ccontr)
        assume "\<not> B"
        then have "\<not> A \<or> \<not> B" by auto 
        from this \<open>\<not>(\<not> A \<or> \<not> B)\<close> show False by auto
      qed
    qed
    with \<open>\<not>(A \<and> B)\<close> show False by auto
  qed

next 
  assume "\<not> A \<or> \<not> B"
  show "\<not> (A \<and> B)"
    sorry
qed


lemma "(\<forall>x y. R x y \<longrightarrow> R y x) \<and> (\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z) \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> (\<forall>x. R x x)"
  sorry


end