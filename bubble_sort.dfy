predicate Ordered(a: array<int>)
  reads a
{
  forall i: int, j:int ::
    0 <= i <= j < a.Length ==>
      a[i] <= a[j]
}

// The bubble sort outputs an ordered list whose elements form the same multiset as the input list
method bubbleSort(a: array<int>)
  modifies a // set array modifiable
  requires a.Length > 0 // array is not empty
  ensures Ordered(a) // ensure the order of the output list
  ensures multiset(a[..]) == old(multiset(a[..])) // ensure input and output form the same multiset
{
  var i := a.Length - 1;
  while i > 0 // the slot for i-th max item, that current loop is working on
    invariant 0 <= i <= a.Length - 1
    invariant forall ii, jj :: i < ii <= jj < a.Length ==> a[ii] <= a[jj] // total order of 1 to (i-1)-th max items
    invariant forall ii, jj :: i < ii < a.Length && 0 <= jj <= i ==> a[jj] <= a[ii] // partial order between max i-1 items and remains
    invariant multiset(a[..]) == old(multiset(a[..])) // same multiset after a loop
  {
    for k := 0 to i
      invariant 0 <= k <= i && k + 1 <= a.Length
      invariant forall ii, jj :: i < ii <= jj < a.Length ==> a[ii] <= a[jj] // total order of 1 to (i-1)-th max items
      invariant forall ii, jj :: i < ii < a.Length && 0 <= jj <= i ==> a[jj] <= a[ii] // partial order between max i-1 items and remains
      invariant forall kk :: 0 <= kk <= k ==> a[kk] <= a[k] // current bubbled item is the maximum among all previous items
      invariant multiset(a[..]) == old(multiset(a[..])) // same multiset after a loop
    {
      if a[k] > a[k + 1] {
        a[k], a[k + 1] := a[k + 1], a[k]; // swap into a[k] <= a[k+1]
      }
    }
    i := i - 1;
  }
}