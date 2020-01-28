
-- Function expression are terms that have types
#check band 
#check nat.add
#check string.append

-- Function application expressions are terms that have types
#check band tt tt
#check nat.add 2 3
#check string.append "I love " "logic!"

-- Function application expessions reduce to return values
#eval band tt tt
#eval nat.add 2 3
#eval string.append "I love " "logic!"

-- Lean strictly and statically enforces typing 
#check band ff "Hi!"
#check nat.add 4 tt
#eval string.append "I love " 5 -- strange error, same problem
