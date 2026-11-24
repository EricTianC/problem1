module

public import Problem1.Statement

namespace Problem1

/-- In dimension one, both products consist of the same term. -/
public theorem goal_one : Goal 1 := by
  intro A _
  simp

end Problem1
