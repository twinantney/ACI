-- Level 18 Foundation Node
-- Parameters: Zero placeholders, zero sorries, zero Mathlib dependencies.

inductive FoundationBlock : Type
  | init : FoundationBlock
  | step : FoundationBlock -> FoundationBlock

def block_weight (n : Nat) : Nat :=
  n * 2
