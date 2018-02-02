function method unpair ( i : nat ) : (nat,nat)
decreases i
{
 if i == 0 then
        (0,0)
    else
        if (unpair(i-1).1) == 0 then (0,(unpair(i-1).0) +1) else (((unpair(i-1).0) +1,(unpair(i-1).1) - 1))
}
function method pick ( i : nat ) : nat

{

var (x , y ) := unpair ( i );
x + i * y

} 

function method cal(a: nat, b: nat ) : nat
ensures unpair(cal(a,b))==(a,b)
decreases a+b,a
{
  if a==0 && b==0 then 0 else if a==0 then cal(b-1,a)+1 else cal(a-1,b+1)+1
}
method catchTheSpy ( a : nat , b : nat )
{
var i: nat := 0;
ghost var t1 :nat :| t1==cal(a,b) && (unpair(t1).0)==a && (unpair(t1).1)==b;
while ((a + i * b) != pick(i))
invariant t1-i>=0
decreases t1-i
  {
    i := i + 1;
  }
}
