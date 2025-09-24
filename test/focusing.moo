{* the first letcc should fire, then the second *}

[ (pair (letcc 'a -> [b 'a]) (letcc 'a -> [b 'a])) 'halt ]