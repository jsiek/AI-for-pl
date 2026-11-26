set a 1
expr 1.5 * 3
expr 10 / 4
set nope
puts $nope
nocmd 1 2
set b [nocmd 3]
set
proc f {X} {return 1}
f 1
proc g {x} {return $x}
g
g 1 2
g 42
puts -nonewline hi
puts there
