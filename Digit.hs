module Digit where

data Half a = Half a a a deriving (Eq)
data Digit a = D1 a
             | D2 a a
             | D3 a a a
             | D4 a a a a 
             | D5 a a a a a

single x = D1 x

push x (D5 a b c d e) = Right (D3 x a b, Half c d e)
push x (D4 a b c d) = Left $ D5 x a b c d
push x (D3 a b c) = Left $ D4 x a b c
push x (D2 a b) = Left $ D3 x a b
push x (D1 a) = Left $ D2 x a

pop (D1 a) = (a,Nothing)
pop (D2 a b) = (a,Just $ D1 b )
pop (D3 a b c) = (a,Just $ D2 b c)
pop (D4 a b c d) = (a,Just $ D3 b c d)
pop (D5 a b c d e) = (a,Just $ D4 b c d e)

splitD (D1 x) = Left x
splitD (D2 x y) = Right (D1 x,D1 y)
splitD (D3 x y z) = Right (D1 x, D2 y z)
splitD (D4 w x y z) = Right (D2 w x, D2 y z)
splitD (D5 v w x y z) = Right (D3 v w x, D2 y z)

fromHalf (Half a b c) = D3 a b c

inject (D5 a b c d e) x = Right (Half a b c, D3 d e x)
inject (D4 a b c d) x = Left $ D5 a b c d x
inject (D3 a b c) x = Left $ D4 a b c x
inject (D2 a b) x = Left $ D3 a b x
inject (D1 a) x = Left $ D2 a x

eject (D1 a) = (Nothing,a)
eject (D2 b a) = (Just $ D1 b,a)
eject (D3 b c a) = (Just $ D2 b c,a)
eject (D4 b c d a) = (Just $ D3 b c d,a)
eject (D5 b c d e a) = (Just $ D4 b c d e,a)
