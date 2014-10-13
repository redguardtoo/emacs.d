(*
      Example proof document for Isabelle/Isar Proof General.
   
      Example.thy,v 12.0 2011/10/13 10:54:50 da Exp
*)


theory Example imports Main begin

text {* Proper proof text -- \textit{naive version}. *}

theorem and_comms: "A & B --> B & A"
proof
  assume "A & B"
  then show "B & A"
  proof
    assume "B" and "A"
    then show ?thesis ..
 qed
qed

text {* Unstructured proof script. *}

theorem  "A & B --> B & A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply assumption
done


end
