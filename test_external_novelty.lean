namespace NoveltySystem
  def foreign_scale (n : Nat) : Nat := n + 8
  theorem novelty_invariant (n : Nat) : foreign_scale n + 0 = foreign_scale n := by rfl
end NoveltySystem