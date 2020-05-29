package daikon;

public class PredIDValPair {

  private int pred_id;
  private int val;

  public PredIDValPair(int pred_id, int val) {
    this.pred_id = pred_id;
    this.val = val;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(this.pred_id);
    sb.append(", ");
    sb.append(this.val);
    return sb.toString();
  }

  public int pred_id() {
    return this.pred_id;
  }

  public int val() {
    return this.val;
  }
}
