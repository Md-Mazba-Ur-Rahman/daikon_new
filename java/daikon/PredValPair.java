package daikon;

import daikon.inv.Invariant;

public class PredValPair {

  private Invariant inv;
  private boolean val;

  public PredValPair(Invariant inv, boolean val) {
    this.inv = inv;
    this.val = val;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(this.inv);
    sb.append(", ");
    sb.append(this.val);
    return sb.toString();
  }

  public Invariant pred() {
    return this.inv;
  }

  public boolean val() {
    return this.val;
  }
}
