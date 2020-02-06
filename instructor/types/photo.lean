structure Photo : Type :=
photo :: (caption : string) (filename : string) (rating : ℕ)

open Photo

def p1 := photo "a caption" "a_file/foo.jpg" 5

#eval p1.caption
#eval p1.filename
#eval p1.rating

def change_rating : Photo → ℕ → Photo :=
λ p n, 
    photo p.caption p.filename n

def p2 := change_rating p1 3

#eval p2.caption
#eval p2.filename
#eval p2.rating