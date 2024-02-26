theory UIDT1 
  imports Main 
begin 

(*znam da vazi konjunkicija \<Rightarrow> vaze oba *)

lemma "p \<and> q \<longrightarrow> p \<or> q"
  apply (rule impI) (*uvodjenje implikacije*)
  apply (erule conjE) 
  apply (rule disjI1) (*stigli smo do aksiome - ona se nalazi u pretpostavci *)
  apply assumption
  done


lemma "q \<longrightarrow> p \<or> q"
  apply (rule impI)
  apply (rule disjI2)
  apply (assumption)
  done

lemma "((p \<and> q) \<longrightarrow> r ) \<longleftrightarrow> (p \<longrightarrow> (q \<longrightarrow> r))"
  apply (rule iffI) (* uvodjenje ekvivalencije *)
   apply (rule impI) 
   apply (rule impI) 
   apply (erule impE)
    apply (rule conjI)
     apply (assumption)
    apply assumption
   apply assumption 
  apply (rule impI)
  apply (erule conjE)
  apply (erule impE)
   apply (assumption)
  apply (erule impE)
   apply (assumption)
  apply (assumption)
  done

lemma "\<not>(A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
  apply (rule impI)
  apply (rule conjI)
   apply (rule notI) (*setaju negaciju*)
   apply (erule notE)
   apply (rule disjI1)
   apply (assumption)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply (assumption)
  done 




end 