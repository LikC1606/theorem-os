lemma checked0 : ∀ w ∈ table0.map Prod.fst, rowOK w := by decide
lemma checked1 : ∀ w ∈ table1.map Prod.fst, rowOK w := by decide
lemma checked2 : ∀ w ∈ table2.map Prod.fst, rowOK w := by decide
lemma checked3 : ∀ w ∈ table3.map Prod.fst, rowOK w := by decide
lemma checked4 : ∀ w ∈ table4.map Prod.fst, rowOK w := by decide
lemma checked5 : ∀ w ∈ table5.map Prod.fst, rowOK w := by decide
lemma checked6 : ∀ w ∈ table6.map Prod.fst, rowOK w := by decide
lemma checked7 : ∀ w ∈ table7.map Prod.fst, rowOK w := by decide
lemma checked8 : ∀ w ∈ table8.map Prod.fst, rowOK w := by decide
lemma checked9 : ∀ w ∈ table9.map Prod.fst, rowOK w := by decide
lemma checked10 : ∀ w ∈ table10.map Prod.fst, rowOK w := by decide
lemma checked11 : ∀ w ∈ table11.map Prod.fst, rowOK w := by decide
lemma checked12 : ∀ w ∈ table12.map Prod.fst, rowOK w := by decide
lemma checked13 : ∀ w ∈ table13.map Prod.fst, rowOK w := by decide
lemma checked14 : ∀ w ∈ table14.map Prod.fst, rowOK w := by decide
lemma checked15 : ∀ w ∈ table15.map Prod.fst, rowOK w := by decide
lemma checked16 : ∀ w ∈ table16.map Prod.fst, rowOK w := by decide
lemma checked17 : ∀ w ∈ table17.map Prod.fst, rowOK w := by decide
lemma checked18 : ∀ w ∈ table18.map Prod.fst, rowOK w := by decide
lemma checked19 : ∀ w ∈ table19.map Prod.fst, rowOK w := by decide
lemma checked20 : ∀ w ∈ table20.map Prod.fst, rowOK w := by decide
lemma checked21 : ∀ w ∈ table21.map Prod.fst, rowOK w := by decide
lemma checked22 : ∀ w ∈ table22.map Prod.fst, rowOK w := by decide
lemma checked23 : ∀ w ∈ table23.map Prod.fst, rowOK w := by decide
lemma checked24 : ∀ w ∈ table24.map Prod.fst, rowOK w := by decide
lemma checked25 : ∀ w ∈ table25.map Prod.fst, rowOK w := by decide
lemma checked26 : ∀ w ∈ table26.map Prod.fst, rowOK w := by decide
lemma checked27 : ∀ w ∈ table27.map Prod.fst, rowOK w := by decide
lemma checked28 : ∀ w ∈ table28.map Prod.fst, rowOK w := by decide
lemma checked29 : ∀ w ∈ table29.map Prod.fst, rowOK w := by decide
lemma checked30 : ∀ w ∈ table30.map Prod.fst, rowOK w := by decide

lemma table_checked : ∀ w ∈ states, rowOK w := by
  simp only [states, table, List.map_append, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨checked0, checked1⟩, checked2⟩, checked3⟩, checked4⟩, checked5⟩, checked6⟩, checked7⟩, checked8⟩, checked9⟩, checked10⟩, checked11⟩, checked12⟩, checked13⟩, checked14⟩, checked15⟩, checked16⟩, checked17⟩, checked18⟩, checked19⟩, checked20⟩, checked21⟩, checked22⟩, checked23⟩, checked24⟩, checked25⟩, checked26⟩, checked27⟩, checked28⟩, checked29⟩, checked30⟩

lemma source_checked : normalize [Vertex.up 0 0] ∈ states := by decide
