variables A : Type 
variables PP QQ : A → Prop  

theorem dm_pred : ¬ (∃ x : A, (PP x ∨ QQ x)) → ∀ x : A, (¬ PP x ∧ ¬ QQ x) :=
begin
  -- Step 1: Introduce assumptions and goal
  assume h x,      -- 1. Assume h : ¬ (∃ x : A, (PP x ∨ QQ x))  
                   --    and take an arbitrary x : A
  constructor,     -- 2. Goal is to prove ¬ PP x ∧ ¬ QQ x,
                   --    so use constructor to split it into two parts

  -- Step 2: Prove ¬ PP x
  assume hp,       -- 1. Assume PP x holds
  apply h,         -- 2. Try to derive a contradiction using h
  constructor,     -- 3. Construct an existential statement ∃ x, (PP x ∨ QQ x)
  left,            -- 4. Choose the left side of the disjunction (PP x)
  exact hp,        -- 5. Directly use the assumption PP x

  -- Step 3: Prove ¬ QQ x
  assume hq,       -- 1. Assume QQ x holds
  apply h,         -- 2. Try to derive a contradiction using h
  constructor,     -- 3. Construct an existential statement ∃ x, (PP x ∨ QQ x)
  right,           -- 4. Choose the right side of the disjunction (QQ x)
  exact hq,        -- 5. Directly use the assumption QQ x
end
