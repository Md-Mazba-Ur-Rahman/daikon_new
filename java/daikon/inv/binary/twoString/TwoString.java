package daikon.inv.binary.twoString;

import daikon.*;
import daikon.inv.*;
import daikon.inv.Invariant.OutputFormat;
import daikon.inv.binary.BinaryInvariant;

import utilMDE.*;

/**
 * Abstract base class used for comparing two strings
 **/

public abstract class TwoString
  extends BinaryInvariant
{
  // We are Serializable, so we specify a version to allow changes to
  // method signatures without breaking serialization.  If you add or
  // remove fields, you should change this number to the current date.
  static final long serialVersionUID = 20020122L;

  protected TwoString(PptSlice ppt) {
    super(ppt);
  }

  public VarInfo var1() {
    return ppt.var_infos[0];
  }

  public VarInfo var2() {
    return ppt.var_infos[1];
  }

  public void add(Object val1, Object val2, int mod_index, int count) {
    // Tests for whether a value is missing should be performed before
    // making this call, so as to reduce overall work.
    Assert.assertTrue(! falsified);
    Assert.assertTrue((mod_index >= 0) && (mod_index < 4));
    // [INCR] Assert.assertTrue(!finished);
    String v1 = (String) val1;
    String v2 = (String) val2;
    if (mod_index == 0) {
      add_unmodified(v1, v2, count);
    } else {
      add_modified(v1, v2, count);
    }
  }

  /**
   * This method need not check for falsified;
   * that is done by the caller.
   **/
  public abstract void add_modified(String v1, String v2, int count);

  /**
   * By default, do nothing if the value hasn't been seen yet.
   * Subclasses can override this.
   **/
  public void add_unmodified(String v1, String v2, int count) {
    return;
  }

}
