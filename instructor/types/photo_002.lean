


structure Photo : Type :=
mk :: (caption : string) (filename : string) (rating : ℕ )

def change_rating : Photo → ℕ → Photo :=
    λ p n, Photo.mk p.caption p.filename n

def change_caption : Photo → string → Photo :=
    λ p s, Photo.mk s p.filename p.rating

def change_filename : Photo → string → Photo :=
    λ p s, Photo.mk p.caption s p.rating


def cat := Photo.mk "Nifty" "nifty.jpg" 5
def selfie := Photo.mk "Aren't I great" "selfie.jpg" 9
#eval cat.filename


