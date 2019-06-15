TEST /// --isSimpleNormalCrossing
R = ZZ/7[x,y,z];
assert(isSimpleNormalCrossing(x^3*y^2) == true);
assert(isSimpleNormalCrossing(x^3*y^2, IsLocal=>true) == true);
assert(isSimpleNormalCrossing(x^2-y^2) == true);
assert(isSimpleNormalCrossing(x^2-y^2, IsLocal=>true) == true);
assert(isSimpleNormalCrossing(x*y*(x-y)) == false);
assert(isSimpleNormalCrossing(x*y*(x-y), IsLocal=>true) == false);
assert(isSimpleNormalCrossing(x^2-y*z) == false);
assert(isSimpleNormalCrossing(x^2-y*z, IsLocal=>true) == false);
///

TEST /// --local vs non-local testing
R = QQ[x,y,z];
f = (y - (x-1)^2)*y^2; --SNC at the origin, but not globally
assert(isSimpleNormalCrossing(f) == true);
assert(isSimpleNormalCrossing(f, IsLocal=>false)==false);
g = (y-1)^2+(x-7)^2 --doesn't even pass through the origin
assert(isSimpleNormalCrossing(g) == true);
assert(isSimpleNormalCrossing(g, IsLocal=>false) == false);
h = x*y^2*(x+1)^3*(y-1)^4; --SNC everywhere
assert(isSimpleNormalCrossing(h) == true);
assert(isSimpleNormalCrossing(h, IsLocal=>false) == true);
w = x*y*((x-1)^2+(z-1)^3); --not SNC everywhere, but is at the origin
assert(isSimpleNormalCrossing(w) == true);
assert(isSimpleNormalCrossing(w, IsLocal=>false) == false);
v = x*(x-1)*(x-2)*(x-3)*(x-4)*(x-5); --vertical lines, SNC everywhere
assert(isSimpleNormalCrossing(v) == true);
assert(isSimpleNormalCrossing(v, IsLocal=>false) == true);
///

TEST ///--a more complicated object, requiring look at a deeper strata
R = ZZ/101[x,y,z];
assert(isSimpleNormalCrossing(x*y*((x+y)-z^2)) == false);
assert(isSimpleNormalCrossing(x*y*((x+y)-z^2), IsLocal=>false) == false);
assert(isSimpleNormalCrossing(x*((x+y)-z^2)) == true);
assert(isSimpleNormalCrossing(x*((x+y)-z^2), IsLocal=>false) == true);
///
