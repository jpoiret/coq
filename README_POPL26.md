This artifact contains the implementation of sort elimination constraints and an 
initial prelude of Rocq making use of it. Refer to `README.md` for instruction on how 
to build from sources. 

The adapted prelude of the core library is in `theories/Init`. 
See in particular `theories/Init/Specif.v` and `theories/Init/Datatypes.v` for 
adaptation of core definitions like the option type. 
The files in `theories/_popl26-examples` support the sections on large elimination 
and the extracted sorts of the paper. 