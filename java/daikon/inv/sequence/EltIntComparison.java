package daikon.inv.sequence;

import daikon.*;
import daikon.inv.*;


// This compares adjacent elements in the sequence.
// Also see NonEqual, NonAliased
class EltIntComparison extends SingleSequence {

  final static boolean debugEltIntComparison = false;

  boolean can_be_eq = false;
  boolean can_be_lt = false;
  boolean can_be_gt = false;

  protected EltIntComparison(PptSlice ppt_) {
    super(ppt_);
  }

  public static EltIntComparison instantiate(PptSlice ppt) {
    return new EltIntComparison(ppt);
  }

/// "Obvious" comparisons

// self.comparison_obvious = None
// # These variables are set to the name of the sequence, or None.
// # Avoid regular expressions wherever possible.
// min1 = (var1[0:4] == "min(") and var1[4:-1]
// max1 = (var1[0:4] == "max(") and var1[4:-1]
// # I think "find" does a regexp operation, unfortunately
// aref1 = string.find(var1, "[")
// if aref1 == -1:
//     aref1 = None
// else:
//     aref1 = var1[0:aref1]
// if min1 or max1 or aref1:
//     min2 = (var2[0:4] == "min(") and var2[4:-1]
//     max2 = (var2[0:4] == "max(") and var2[4:-1]
//     aref2 = string.find(var2, "[")
//     if aref2 == -1:
//         aref2 = None
//     else:
//         aref2 = var2[0:aref2]
//     if min1 and max2 and min1 == max2:
//         self.comparison_obvious = "<="
//     elif min1 and aref2 and min1 == aref2:
//         self.comparison_obvious = "<="
//     elif max1 and min2 and max1 == min2:
//         self.comparison_obvious = ">="
//     elif max1 and aref2 and max1 == aref2:
//         self.comparison_obvious = ">="
//     elif aref1 and min2 and aref1 == min2:
//         self.comparison_obvious = ">="
//     elif aref1 and max2 and aref1 == max2:
//         self.comparison_obvious = "<="

  public String repr() {
    double probability = getProbability();
    return "EltIntComparison(" + var().name + "): "
      + "can_be_eq=" + can_be_eq
      + ",can_be_lt=" + can_be_lt
      + ",can_be_gt=" + can_be_gt
      + "; probability = " + probability;
  }

  public String format() {
    if (justified() && (can_be_eq || can_be_gt || can_be_lt)) {
      String inequality = (can_be_lt ? "<" : can_be_gt ? ">" : "");
      String comparison = (can_be_eq ? "=" : "");
      if (debugEltIntComparison) {
        System.out.println(repr()
                           + "; inequality=\"" + inequality + "\""
                           + ",comparison=\"" + comparison + "\"");
      }
      return (var().name + " intra-sequence ordering: "
              + inequality + comparison);
    } else {
      return null;
    }
  }


  public void add_modified(int[] a, int count) {
    for (int i=1; i<a.length; i++) {
      int v1 = a[i-1];
      int v2 = a[i];
      if (v1 == v2)
        can_be_eq = true;
      else if (v1 < v2)
        can_be_lt = true;
      else
        can_be_gt = true;
    }
    if (can_be_lt && can_be_gt) {
      destroy();
      return;
    }
  }

  protected double computeProbability() {
    if (no_invariant) {
      return Invariant.PROBABILITY_NEVER;
    } else if (can_be_lt || can_be_gt) {
      return Math.pow(.5, ppt.num_values());
    } else {
      return 0;
    }
  }

}
