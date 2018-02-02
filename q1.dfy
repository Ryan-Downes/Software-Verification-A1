predicate sorted(l1: int, u1: int,a: array<int>)
	requires a != null &&  u1 < a.Length 
	reads a
{
	forall i,j::  (0 <= i && l1 <= i <= j <= u1) ==> a[i] <= a[j]
}

method insertSort(a : array<int>)
    requires a != null
    modifies a
    ensures sorted(0, a.Length - 1,a)
{
    
    var i := 1;
    
    while (i < a.Length)
        invariant (0 <= i - 1 < a.Length && sorted(0,i - 1,a)) || a.Length == 0
        {
            var j := i;
            
            var value := a[i];
            a[i] := a[i-1];
            while (j > 0 && a[j-1] > value)
                invariant forall m:: 0 <= j < m <= i <= a.Length ==> a[m] >= value 
                invariant sorted(0,i,a)
            {
                a[j] := a[j-1];
                j := j - 1;
                
            }
            a[j] := value;
            i := i + 1;
        }
}
