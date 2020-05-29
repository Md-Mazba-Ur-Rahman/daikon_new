package daikon;

import static daikon.Global.lineSep;

import daikon.config.Configuration;
import daikon.inv.Invariant;
import daikon.inv.InvariantStatus;
import daikon.inv.OutputFormat;
import daikon.inv.ValueSet;
import daikon.suppress.NIS;
import gnu.getopt.Getopt;
import gnu.getopt.LongOpt;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.apache.commons.csv.CSVFormat;
import org.apache.commons.csv.CSVPrinter;
import org.checkerframework.checker.interning.qual.Interned;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.checker.signature.qual.ClassGetName;
import org.checkerframework.dataflow.qual.Pure;
import org.plumelib.util.EntryReader;
import org.plumelib.util.RegexUtil;
import org.plumelib.util.UtilPlume;

/**
 * DaikonSimple reads a declaration file and trace file and outputs a list of likely invariants
 * using the simple incremental algorithm. Its methods parallel those of Daikon but oftentimes
 * certain checks are eliminated from DaikonSimple's methods because there is less filtering of
 * invariants and variables.
 *
 * <p>DaikonSimple was written to check the implementation of the optimizations in Daikon.
 * DaikonSimple does not use an optimizations, and its processing will produce a complete set of
 * true invariants. Daikon does have flags to "turn off" some of its optimizations but there are
 * some optimizations are built into the way Daikon processes the samples (e.g. variable hierarchy
 * and bottom up processing). In addition, we want to check the optimizations, so we don't want to
 * bypass them. In Daikon, code was written to "undo" the optimizations, so we could recover the
 * invariants that were previously filtered out or not created (see Daikon.dkconfig_undo_opts flag).
 * By comparing the output from the two, we can find problems with the optimization implementation
 * by tracking the cause of the differences.
 */
@SuppressWarnings("nullness") // not actively maintained
public class DataGen {

  // logging information
  public static final Logger debug = Logger.getLogger("daikon.DataGen");

  public static final Logger debug_detail = Logger.getLogger("daikon.DataGen.Detail");

  // // inv file for storing the invariants in serialized form
  // public static File inv_file = null;

  // Command-line options / command-line arguments
  public static final String output_data_dir_OPTION = "out-dir";

  private static String usage =
      String.join(
          lineSep,
          "",
          "Usage: java daikon.DataGen [OPTION]... <decls_file> <dtrace_file>",
          "  -h, --" + Daikon.help_SWITCH,
          "      Display this usage message",
          "  --" + output_data_dir_OPTION + " dir",
          "      Dir where output data is stored",
          // "  -o, <inv_file> ",
          // "      Writes output to <inv_file>",
          "  --" + Daikon.debugAll_SWITCH,
          "      Turns on all debug flags (voluminous output)",
          "  --" + Daikon.debug_SWITCH + " logger",
          "      Turns on the specified debug logger",
          "  --" + Daikon.track_SWITCH + " class<var1,var2,var3>@ppt",
          "      Print debug info on the specified invariant class, vars, and ppt");

  // a pptMap that contains all the program points
  public static PptMap all_ppts;

  public static String output_data_dir;

  public static InvIDManager invIDMan = new InvIDManager();

  public static void main(final String[] args) throws IOException, FileNotFoundException {

    try {
      mainHelper(args);
    } catch (Daikon.DaikonTerminationException e) {
      Daikon.handleDaikonTerminationException(e);
    }
  }

  /**
   * This does the work of {@link #main}, but it never calls System.exit, so it is appropriate to be
   * called programmatically.
   *
   * <p>Difference from {@link daikon.Daikon#mainHelper(String[])}Helper: turn off optimization
   * flags (equality, dynamic constants, NIS suppression).
   */
  public static void mainHelper(final String[] args) throws IOException, FileNotFoundException {

    // set up logging information
    daikon.LogHelper.setupLogs(daikon.LogHelper.INFO);

    // No optimizations used in the simple incremental algorithm so
    // optimizations are turned off.
    Daikon.use_equality_optimization = false;
    DynamicConstants.dkconfig_use_dynamic_constant_optimization = false;
    NIS.dkconfig_enabled = false;

    // The flag tells FileIO and Daikon to use DaikonSimple
    // specific methods (e.g. FileIO.read_declaration_file).
    // When FileIO reads and processes
    // samples, it must use the SimpleProcessor rather than the
    // default Processor.
    Daikon.using_DaikonSimple = true;

    // Read command line options
    Daikon.FileOptions files = DataGen.read_options(args, usage);
    // DaikonSimple does not supply nor use the spinfo_files and map_files
    Set<File> decls_files = files.decls;
    Set<String> dtrace_files = files.dtrace;

    // Set up debug traces; note this comes after reading command line options.
    LogHelper.setupLogs(Global.debugAll ? LogHelper.FINE : LogHelper.INFO);

    if ((decls_files.size() == 0) && (dtrace_files.size() == 0)) {
      throw new Daikon.UserError("No .decls or .dtrace files specified");
    }

    // Create the list of all invariant types
    Daikon.setup_proto_invs();

    // Create the program points for enter and numbered exits and
    // initializes the points (adding orig and derived variables)
    all_ppts = FileIO.read_declaration_files(decls_files);

    // Create the combined exits (and add orig and derived vars)
    // Daikon.create_combined_exits(all_ppts);

    // Read and process the data trace files
    SimpleProcessor processor = new SimpleProcessor();
    FileIO.read_data_trace_files(dtrace_files, all_ppts, processor, true);

    // System.exit(0);

    // Print out the invariants for each program point (sort first)
    for (PptTopLevel ppt : all_ppts.pptIterable()) {

      // We do not need to print out program points that have not seen
      // any samples.
      if (ppt.num_samples() == 0) {
        continue;
      }
      List<Invariant> invs = PrintInvariants.sort_invariant_list(ppt.invariants_vector());
      List<Invariant> filtered_invs = Daikon.filter_invs(invs);
      // The dkconfig_quiet printing is used for creating diffs between
      // DaikonSimple
      // and Daikon's output. The second kind of printing is used for
      // debugging. Since the names of the program points are the same for both
      // Daikon and DaikonSimple, diffing the two output will result in
      // only differences in the invariants, but we can not see at which program
      // points these differing invariants appear. Using the second kind of
      // printing,
      // Daikon's output does not have the '+' in the program point name, so in
      // addition
      // to the invariants showing up in the diff, we will also see the program
      // point
      // names.

      if (Daikon.dkconfig_quiet) {
        System.out.println("====================================================");
        System.out.println(ppt.name());
      } else {
        System.out.println("===================================================+");
        System.out.println(ppt.name() + " +");
      }

      // Sometimes the program points actually differ in number of
      // samples seen due to differences in how Daikon and DaikonSimple
      // see the variable hierarchy.
      System.out.println(ppt.num_samples());

      for (Invariant inv : filtered_invs) {
        System.out.println(inv.getClass());
        System.out.println(inv);
      }
    }
  }

  ///////////////////////////////////////////////////////////////////////////
  // Read in the command line options
  // Return {decls, dtrace, spinfo, map} files.
  protected static Daikon.FileOptions read_options(String[] args, String usage) {
    if (args.length == 0) {
      System.out.println("Error: no files supplied on command line.");
      System.out.println(usage);
      throw new Daikon.UserError();
    }

    // LinkedHashSet because it can be confusing to users if files (of the
    // same type) are gratuitously processed in a different order than they
    // were supplied on the command line.
    HashSet<File> decl_files = new LinkedHashSet<>();
    HashSet<String> dtrace_files = new LinkedHashSet<>(); // file names or "-" or "+"
    HashSet<File> spinfo_files = new LinkedHashSet<>();
    HashSet<File> map_files = new LinkedHashSet<>();

    LongOpt[] longopts =
        new LongOpt[] {
          // Control output
          new LongOpt(Daikon.help_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.no_text_output_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.format_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.show_progress_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.no_show_progress_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.noversion_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.output_num_samples_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.files_from_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.omit_from_output_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          // Control invariant detection
          new LongOpt(Daikon.conf_limit_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.list_type_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.user_defined_invariant_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.disable_all_invariants_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.no_dataflow_hierarchy_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.suppress_redundant_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          // Process only part of the trace file
          new LongOpt(Daikon.ppt_regexp_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.ppt_omit_regexp_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.var_regexp_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.var_omit_regexp_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          // Configuration options
          new LongOpt(Daikon.server_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.config_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.config_option_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          // Debugging
          new LongOpt(Daikon.debugAll_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          new LongOpt(Daikon.debug_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.track_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.disc_reason_SWITCH, LongOpt.REQUIRED_ARGUMENT, null, 0),
          new LongOpt(Daikon.mem_stat_SWITCH, LongOpt.NO_ARGUMENT, null, 0),
          // DateGen configuration
          new LongOpt(output_data_dir_OPTION, LongOpt.REQUIRED_ARGUMENT, null, 0)
        };
    Getopt g = new Getopt("daikon.Daikon", args, "ho:", longopts);
    int c;

    while ((c = g.getopt()) != -1) {
      switch (c) {
        case 0:
          // got a long option
          String option_name = longopts[g.getLongind()].getName();

          // Control output
          if (Daikon.help_SWITCH.equals(option_name)) {
            System.out.println(usage);
            throw new Daikon.NormalTermination();
          } else if (Daikon.no_text_output_SWITCH.equals(option_name)) {
            Daikon.no_text_output = true;
          } else if (Daikon.format_SWITCH.equals(option_name)) {
            String format_name = Daikon.getOptarg(g);
            Daikon.output_format = OutputFormat.get(format_name);
            if (Daikon.output_format == null) {
              throw new Daikon.UserError("Unknown output format:  --format " + format_name);
            }
          } else if (Daikon.show_progress_SWITCH.equals(option_name)) {
            Daikon.show_progress = true;
            LogHelper.setLevel("daikon.Progress", LogHelper.FINE);
          } else if (Daikon.no_show_progress_SWITCH.equals(option_name)) {
            Daikon.show_progress = false;
          } else if (Daikon.noversion_SWITCH.equals(option_name)) {
            Daikon.noversion_output = true;
          } else if (Daikon.output_num_samples_SWITCH.equals(option_name)) {
            Daikon.output_num_samples = true;
          } else if (Daikon.files_from_SWITCH.equals(option_name)) {
            String files_from_filename = Daikon.getOptarg(g);
            try {
              for (String filename : new EntryReader(files_from_filename)) {
                // Ignore blank lines in file.
                if (filename.equals("")) {
                  continue;
                }
                // This code is duplicated below outside the options loop.
                // These aren't "endsWith()" because there might be a suffix
                // on the end (eg, a date, or ".gz").
                File file = new File(filename);
                if (!file.exists()) {
                  throw new Daikon.UserError("File " + filename + " not found.");
                }
                if (filename.indexOf(".decls") != -1) {
                  decl_files.add(file);
                } else if (filename.indexOf(".dtrace") != -1) {
                  dtrace_files.add(filename);
                } else if (filename.indexOf(".spinfo") != -1) {
                  spinfo_files.add(file);
                } else if (filename.indexOf(".map") != -1) {
                  map_files.add(file);
                } else {
                  throw new Daikon.UserError("Unrecognized file extension: " + filename);
                }
              }
            } catch (IOException e) {
              throw new RuntimeException(
                  String.format("Error reading --files_from file: %s", files_from_filename));
            }
            break;
          } else if (Daikon.omit_from_output_SWITCH.equals(option_name)) {
            String f = Daikon.getOptarg(g);
            for (int i = 0; i < f.length(); i++) {
              if ("0rs".indexOf(f.charAt(i)) == -1) {
                throw new Daikon.UserError(
                    "omit_from_output flag letter '" + f.charAt(i) + "' is unknown");
              }
              Daikon.omit_types[f.charAt(i)] = true;
            }
            Daikon.omit_from_output = true;
          }
          // Control invariant detection
          else if (Daikon.conf_limit_SWITCH.equals(option_name)) {
            double limit = Double.parseDouble(Daikon.getOptarg(g));
            if ((limit < 0.0) || (limit > 1.0)) {
              throw new Daikon.UserError(Daikon.conf_limit_SWITCH + " must be between [0..1]");
            }
            Configuration.getInstance()
                .apply("daikon.inv.Invariant.confidence_limit", String.valueOf(limit));
          } else if (Daikon.list_type_SWITCH.equals(option_name)) {
            try {
              String list_type_string = Daikon.getOptarg(g);
              ProglangType.list_implementors.add(list_type_string);
            } catch (Exception e) {
              throw new Daikon.UserError(
                  "Problem parsing " + Daikon.list_type_SWITCH + " option: " + e);
            }
            break;
          } else if (Daikon.user_defined_invariant_SWITCH.equals(option_name)) {
            try {
              String user_defined_invariant_string = Daikon.getOptarg(g);
              Matcher m = Daikon.classGetNamePattern.matcher(user_defined_invariant_string);
              if (!m.matches()) {
                throw new Daikon.UserError(
                    "Bad argument "
                        + user_defined_invariant_string
                        + " for "
                        + Daikon.ppt_regexp_SWITCH
                        + ": not in the format required by Class.getName(String)");
              }
              @SuppressWarnings("signature") // Regex match guarantees the format of Class.getName()
              @ClassGetName String cname = user_defined_invariant_string;
              Daikon.userDefinedInvariants.add(cname);
            } catch (Exception e) {
              throw new Daikon.UserError(
                  "Problem parsing " + Daikon.user_defined_invariant_SWITCH + " option: " + e);
            }
            break;
          } else if (Daikon.disable_all_invariants_SWITCH.equals(option_name)) {
            // There are two possibilities:
            //  * a given invariant class is not yet loaded, in which case
            //    we set the default value for its dkconfig_enabled field.
            //  * a given invariant class is already loaded, in which case
            //    we reflectively set its dkconfig_enabled to false.

            // Set the default for not-yet-loaded invariants.
            Invariant.invariantEnabledDefault = false;

            // Get all loaded classes.  This solution is from
            // http://stackoverflow.com/a/10261850/173852 .  Alternate approach:
            // http://stackoverflow.com/questions/2548384/java-get-a-list-of-all-classes-loaded-in-the-jvm
            Field f;
            try {
              f = ClassLoader.class.getDeclaredField("classes");
            } catch (NoSuchFieldException e) {
              throw new Daikon.BugInDaikon("Didn't find field ClassLoader.classes");
            }
            f.setAccessible(true);
            Object classesAsObject;
            try {
              classesAsObject = f.get(Thread.currentThread().getContextClassLoader());
            } catch (IllegalAccessException e) {
              throw new Daikon.BugInDaikon("Field ClassLoader.classes was not made accessible");
            }
            @SuppressWarnings({
              "unchecked", // type of ClassLoader.classes field is known
              "nullness" // ClassLoader.classes is non-null
            })
            @NonNull List<Class<?>> classes = (List<Class<?>>) classesAsObject;
            for (int i = 0; i < classes.size(); i++) {
              Class<?> loadedClass = classes.get(i);
              if (Invariant.class.isAssignableFrom(loadedClass)) {
                @SuppressWarnings("unchecked") // loadedClass is a subclass of Invariant
                Class<? extends Invariant> invType = (Class<? extends Invariant>) loadedClass;
                try {
                  Field field = invType.getField("dkconfig_enabled");
                  if (field.getType() != Boolean.TYPE) {
                    throw new Daikon.BugInDaikon(
                        "Field "
                            + invType
                            + ".dkconfig_enabled has type "
                            + field.getType()
                            + " instead of boolean");
                  } else {
                    field.set(null, false);
                    // System.out.println(
                    //     "Set field "
                    //         + invType
                    //         + ".dkconfig_enabled to false");
                  }
                } catch (NoSuchFieldException e) {
                  // System.out.println(
                  //     "Class " + invType + " does not have a dkconfig_enabled field");
                } catch (IllegalAccessException e) {
                  throw new Daikon.BugInDaikon(
                      "IllegalAccessException for field " + invType + ".dkconfig_enabled");
                }
              }
            }
          } else if (Daikon.no_dataflow_hierarchy_SWITCH.equals(option_name)) {
            Daikon.use_dataflow_hierarchy = false;
          } else if (Daikon.suppress_redundant_SWITCH.equals(option_name)) {
            Daikon.suppress_redundant_invariants_with_simplify = true;
          }

          // Process only part of the trace file
          else if (Daikon.ppt_regexp_SWITCH.equals(option_name)) {
            if (Daikon.ppt_regexp != null) {
              throw new Daikon.UserError(
                  "multiple --"
                      + Daikon.ppt_regexp_SWITCH
                      + " regular expressions supplied on command line");
            }
            String regexp_string = Daikon.getOptarg(g);
            if (!RegexUtil.isRegex(regexp_string)) {
              throw new Daikon.UserError(
                  "Bad regexp "
                      + regexp_string
                      + " for "
                      + Daikon.ppt_regexp_SWITCH
                      + ": "
                      + RegexUtil.regexError(regexp_string));
            }
            Daikon.ppt_regexp = Pattern.compile(regexp_string);
            break;
          } else if (Daikon.ppt_omit_regexp_SWITCH.equals(option_name)) {
            if (Daikon.ppt_omit_regexp != null) {
              throw new Daikon.UserError(
                  "multiple --"
                      + Daikon.ppt_omit_regexp_SWITCH
                      + " regular expressions supplied on command line");
            }
            String regexp_string = Daikon.getOptarg(g);
            if (!RegexUtil.isRegex(regexp_string)) {
              throw new Daikon.UserError(
                  "Bad regexp "
                      + regexp_string
                      + " for "
                      + Daikon.ppt_omit_regexp_SWITCH
                      + ": "
                      + RegexUtil.regexError(regexp_string));
            }
            Daikon.ppt_omit_regexp = Pattern.compile(regexp_string);
            break;
          } else if (Daikon.var_regexp_SWITCH.equals(option_name)) {
            if (Daikon.var_regexp != null) {
              throw new Daikon.UserError(
                  "multiple --"
                      + Daikon.var_regexp_SWITCH
                      + " regular expressions supplied on command line");
            }
            String regexp_string = Daikon.getOptarg(g);
            if (!RegexUtil.isRegex(regexp_string)) {
              throw new Daikon.UserError(
                  "Bad regexp "
                      + regexp_string
                      + " for "
                      + Daikon.var_regexp_SWITCH
                      + ": "
                      + RegexUtil.regexError(regexp_string));
            }
            Daikon.var_regexp = Pattern.compile(regexp_string);
            break;
          } else if (Daikon.var_omit_regexp_SWITCH.equals(option_name)) {
            if (Daikon.var_omit_regexp != null) {
              throw new Daikon.UserError(
                  "multiple --"
                      + Daikon.var_omit_regexp_SWITCH
                      + " regular expressions supplied on command line");
            }
            String regexp_string = Daikon.getOptarg(g);
            if (!RegexUtil.isRegex(regexp_string)) {
              throw new Daikon.UserError(
                  "Bad regexp "
                      + regexp_string
                      + " for "
                      + Daikon.var_omit_regexp_SWITCH
                      + ": "
                      + RegexUtil.regexError(regexp_string));
            }
            Daikon.var_omit_regexp = Pattern.compile(regexp_string);
            break;
          } else if (Daikon.server_SWITCH.equals(option_name)) {
            String input_dir = Daikon.getOptarg(g);
            Daikon.server_dir = new File(input_dir);
            if (!Daikon.server_dir.isDirectory()
                || !Daikon.server_dir.canRead()
                || !Daikon.server_dir.canWrite()) {
              throw new RuntimeException(
                  "Could not open config file in server directory " + Daikon.server_dir);
            }
            break;

            // Configuration options

          } else if (Daikon.config_SWITCH.equals(option_name)) {
            String config_file = Daikon.getOptarg(g);
            try {
              InputStream stream = new FileInputStream(config_file);
              Configuration.getInstance().apply(stream);
            } catch (IOException e) {
              throw new Daikon.UserError(
                  // Is this the only possible reason for an IOException?
                  "Could not open config file " + config_file);
            }
            break;
          } else if (Daikon.config_option_SWITCH.equals(option_name)) {
            String item = Daikon.getOptarg(g);
            try {
              Configuration.getInstance().apply(item);
            } catch (daikon.config.Configuration.ConfigException e) {
              throw new Daikon.UserError(e);
            }
            break;
          } else if (Daikon.debugAll_SWITCH.equals(option_name)) {
            Global.debugAll = true;
          } else if (Daikon.debug_SWITCH.equals(option_name)) {
            LogHelper.setLevel(Daikon.getOptarg(g), LogHelper.FINE);
          } else if (Daikon.track_SWITCH.equals(option_name)) {
            LogHelper.setLevel("daikon.Debug", LogHelper.FINE);
            String error = Debug.add_track(Daikon.getOptarg(g));
            if (error != null) {
              throw new Daikon.UserError(
                  "Error parsing track argument '" + Daikon.getOptarg(g) + "' - " + error);
            }
          } else if (Daikon.disc_reason_SWITCH.equals(option_name)) {
            try {
              PrintInvariants.discReasonSetup(Daikon.getOptarg(g));
            } catch (IllegalArgumentException e) {
              throw new Daikon.UserError(e);
            }
          } else if (Daikon.mem_stat_SWITCH.equals(option_name)) {
            Daikon.use_mem_monitor = true;
          } else if (output_data_dir_OPTION.equals(option_name)) {
            output_data_dir = Daikon.getOptarg(g);
            File dir = new File(output_data_dir);
            if (!dir.exists()) dir.mkdir();
          } else {
            throw new Daikon.UserError("Unknown option " + option_name + " on command line");
          }
          break;
        case 'h':
          System.out.println(usage);
          throw new Daikon.NormalTermination();
        case 'o':
          String inv_filename = Daikon.getOptarg(g);

          if (Daikon.inv_file != null) {
            throw new Daikon.UserError(
                "multiple serialization output files supplied on command line: "
                    + Daikon.inv_file
                    + " "
                    + inv_filename);
          }

          Daikon.inv_file = new File(inv_filename);

          if (!UtilPlume.canCreateAndWrite(Daikon.inv_file)) {
            throw new Daikon.UserError(
                "Cannot write to serialization output file " + Daikon.inv_file);
          }
          break;
          //
        case '?':
          // break; // getopt() already printed an error
          System.out.println(usage);
          throw new Daikon.NormalTermination();
          //
        default:
          throw new Daikon.BugInDaikon("getopt() returned " + c);
      }
    }

    // This code is duplicated above within the switch processing.
    // First check that all the file names are OK, so we don't do lots of
    // processing only to bail out at the end.
    for (int i = g.getOptind(); i < args.length; i++) {
      String filename = args[i];
      if (filename.equals("-") || filename.equals("+")) {
        dtrace_files.add(filename);
        continue;
      }

      File file = new File(filename);
      if (!file.exists()) {
        throw new Daikon.UserError("File " + file + " not found.");
      }
      filename = file.toString();

      // These aren't "endsWith()" because there might be a suffix on the end
      // (eg, a date or ".gz").
      if (filename.indexOf(".decls") != -1) {
        decl_files.add(file);
      } else if (filename.indexOf(".dtrace") != -1) {
        dtrace_files.add(filename);
        // Always output an invariant file by default, even if none is
        // specified on the command line.
        if (Daikon.inv_file == null) {
          String basename;
          // This puts the .inv file in the current directory.
          basename = new File(filename).getName();
          // This puts the .inv file in the same directory as the .dtrace file.
          // basename = filename;
          int base_end = basename.indexOf(".dtrace");
          String inv_filename = basename.substring(0, base_end) + ".inv.gz";

          Daikon.inv_file = new File(inv_filename);
          if (!UtilPlume.canCreateAndWrite(Daikon.inv_file)) {
            throw new Daikon.UserError("Cannot write to file " + Daikon.inv_file);
          }
        }
      } else if (filename.indexOf(".spinfo") != -1) {
        spinfo_files.add(file);
      } else if (filename.indexOf(".map") != -1) {
        map_files.add(file);
      } else {
        throw new Daikon.UserError("Unrecognized file type: " + file);
      }
    }

    // Set the fuzzy float comparison ratio.  This needs to be done after
    // any configuration options (which may set the ratio) are processed.
    Global.fuzzy.setRelativeRatio(Invariant.dkconfig_fuzzy_ratio);

    // Setup ppt_max_name based on the specified percentage of ppts to process
    if (Daikon.dkconfig_ppt_perc != 100) {
      Daikon.ppt_max_name = Daikon.setup_ppt_perc(decl_files, Daikon.dkconfig_ppt_perc);
      System.out.println("Max ppt name = " + Daikon.ppt_max_name);
    }

    // Validate guardNulls option
    PrintInvariants.validateGuardNulls();

    return new Daikon.FileOptions(decl_files, dtrace_files, spinfo_files, map_files);
  }

  /**
   * Install views and the invariants. Duplicated from PptTopLevel's version because DaikonSimple
   * needs to use its own version of slice checking code.
   *
   * <p>Difference from PptTopLevel's version:
   *
   * <ol>
   *   <li>canonical (leader of equality set) check of variables is turned off because every
   *       variable is in its own equality set
   *   <li>debugging information turned off because DaikonSimple's code is more contained
   *   <li>less constraints on the slices
   * </ol>
   *
   * @see daikon.PptTopLevel#instantiate_views_and_invariants()
   */

  // Note that some slightly inefficient code has been added to aid
  // in debugging. When creating binary and ternary views and debugging
  // is on, the outer loops will not terminate prematurely on inappropriate
  // (i.e., non-canonical) variables. This allows explicit debug statements
  // for each possible combination, simplifying determining why certain
  // slices were not created.
  //
  // Note that '///*' indicates code duplicated from PptTopLevel's
  // version but commented out because DaikonSimple does not need
  // to perform these checks
  public static void instantiate_views_and_invariants(PptTopLevel ppt) {

    // used only for debugging
    int old_num_vars = ppt.var_infos.length;
    int old_num_views = ppt.numViews();
    boolean debug_on = debug.isLoggable(Level.FINE);

    // / 1. all unary views

    // Unary slices/invariants.
    // Currently, there are no constraints on the unary
    // slices. Since we are trying to create all of the invariants, the
    // variables does not have to be a leader and can be a constant.
    // Note that the always missing check is only applicable when the
    // dynamic constants optimization is turned on (so we do not do the
    // check here).

    List<PptSlice> unary_views = new ArrayList<>(ppt.var_infos.length);
    for (VarInfo vi : ppt.var_infos) {

      // /* if (!is_slice_ok(vi))
      // /* continue;

      PptSlice1 slice1 = new PptSlice1(ppt, vi);
      slice1.instantiate_invariants();

      unary_views.add(slice1);
    }
    ppt.addViews(unary_views);
    unary_views = null;

    // / 2. all binary views

    // Binary slices/invariants.
    List<PptSlice> binary_views = new ArrayList<>();
    for (int i1 = 0; i1 < ppt.var_infos.length; i1++) {
      VarInfo var1 = ppt.var_infos[i1];

      // Variables can be constant and missing in DaikonSimple invariants
      // /* if (!is_var_ok_binary(var1))
      // /* continue;

      for (int i2 = i1; i2 < ppt.var_infos.length; i2++) {
        VarInfo var2 = ppt.var_infos[i2];

        // Variables can be constant and missing in DaikonSimple invariants
        // /* if (!is_var_ok_binary(var2))
        // /* continue;

        if (!(var1.compatible(var2)
            || (var1.type.isArray() && var1.eltsCompatible(var2))
            || (var2.type.isArray() && var2.eltsCompatible(var1)))) {
          continue;
        }

        PptSlice2 slice2 = new PptSlice2(ppt, var1, var2);
        slice2.instantiate_invariants();

        binary_views.add(slice2);
      }
    }
    ppt.addViews(binary_views);
    binary_views = null;

    // 3. all ternary views
    List<PptSlice> ternary_views = new ArrayList<>();
    for (int i1 = 0; i1 < ppt.var_infos.length; i1++) {
      VarInfo var1 = ppt.var_infos[i1];

      if (!is_var_ok(var1)) {
        continue;
      }

      for (int i2 = i1; i2 < ppt.var_infos.length; i2++) {
        VarInfo var2 = ppt.var_infos[i2];

        if (!is_var_ok(var2)) {
          continue;
        }

        for (int i3 = i2; i3 < ppt.var_infos.length; i3++) {
          VarInfo var3 = ppt.var_infos[i3];

          if (!is_var_ok(var3)) {
            continue;
          }

          if (!is_slice_ok(var1, var2, var3)) {
            continue;
          }
          PptSlice3 slice3 = new PptSlice3(ppt, var1, var2, var3);
          slice3.instantiate_invariants();
          ternary_views.add(slice3);
        }
      }
    }

    ppt.addViews(ternary_views);

    // This method didn't add any new variables.
    assert old_num_vars == ppt.var_infos.length;
    ppt.repCheck();
  }

  // This method is exclusively for checking variables participating
  // in ternary invariants. The variable must be integer or float, and
  // can not be an array.
  @Pure
  public static boolean is_var_ok(VarInfo var) {

    return (var.file_rep_type.isIntegral() || var.file_rep_type.isFloat())
        && !var.rep_type.isArray();
  }

  /**
   * Returns whether or not the specified binary slice should be created. The slice should not be
   * created if the vars are not compatible.
   *
   * <p>Since we are trying to create all of the invariants, the variables does not have to be a
   * leader and can be a constant. Note that the always missing check is only applicable when the
   * dynamic constants optimization is turned on (so we do not do the check here).
   *
   * @see daikon.PptTopLevel#is_slice_ok(VarInfo, VarInfo)
   */
  @Pure
  public static boolean is_slice_ok(VarInfo v1, VarInfo v2) {

    return v1.compatible(v2);
  }

  /**
   * Returns whether or not the specified ternary slice should be created. The slice should not be
   * created if any of the following are true
   *
   * <ul>
   *   <li>Any var is an array
   *   <li>Any of the vars are not compatible with the others
   *   <li>Any var is not (integral or float)
   * </ul>
   *
   * Since we are trying to create all of the invariants, the variables does not have to be a leader
   * and can be a constant. Note that the always missing check is only applicable when the dynamic
   * constants optimization is turned on (so we do not do the check here). In addition, we do want
   * to create the reflexive ones and partially reflexive invariants.
   *
   * @see daikon.PptTopLevel#is_slice_ok(VarInfo, VarInfo, VarInfo)
   */
  @Pure
  public static boolean is_slice_ok(VarInfo v1, VarInfo v2, VarInfo v3) {

    // Vars must be compatible
    return (v1.compatible(v2) && v1.compatible(v3) && v2.compatible(v3));
  }

  /**
   * The Call class helps the SimpleProcessor keep track of matching enter and exit program points
   * and also object program points. Each Call object represents one entry in the dtrace file, i.e.
   * enter, exit, object entry.
   */
  static final class Call {

    public PptTopLevel ppt;

    public ValueTuple vt;

    public Call(PptTopLevel ppt, ValueTuple vt) {

      this.ppt = ppt;
      this.vt = vt;
    }
  }

  /** The SimpleProcessor class processes each sample in the dtrace file. */
  public static class SimpleProcessor extends FileIO.Processor {
    PptMap all_ppts;

    /** nonce -> List<Call,Call> * */
    // The first Call is the enter entry and the second is the object entry
    Map<Integer, List<Call>> call_map = new LinkedHashMap<>();

    // Flag for whether there are out of order entries in the
    // dtrace file. For unterminated calls (enter but
    // not exit entry in the dtrace file), because DaikonSimple had
    // processed each entry separately (not bottom up like Daikon),
    // DaikonSimple applied the enter and object call before seeing the
    // exit call, which is not consistent with Daikon. Daikon does not
    // process unterminated method calls.

    // The method of holding the enter and object calls until finding
    // a matching exit call assumes:
    // - enter always comes before exit
    // - first entry in dtrace is an enter
    // - order in dtrace is enter, exit, object [for constructors] or
    // enter, object, exit, object [for methods] but not necessarily
    // sequential
    boolean wait = false;

    // pointer to last nonce so we can associate the object entry
    // with the right enter entry
    Integer last_nonce = -1;

    /**
     * Creates a ValueTuple for the receiver using the vt of the original. The method copies over
     * the values of variables shared by both program points and sets the rest of the variables in
     * the receiver's ValueTuple as missing. Also, adds the orig and derived variables to the
     * receiver and returns the newly created ValueTuple.
     */
    private static ValueTuple copySample(
        PptTopLevel receiver, PptTopLevel original, ValueTuple vt, int nonce) {

      // Make the vt for the receiver ppt
      //      Object[] values = new Object[receiver.num_tracevars];
      //      int[] mods = new int[receiver.num_tracevars];
      @Nullable @Interned Object[] values =
          new @Interned Object[receiver.var_infos.length - receiver.num_static_constant_vars];
      int[] mods = new int[receiver.var_infos.length - receiver.num_static_constant_vars];

      // Build the vt for the receiver ppt by looking through the current
      // vt and filling in the gaps.
      int k = 0;
      for (VarInfo var : receiver.var_infos) {
        if (var.is_static_constant) {
          continue;
        }
        boolean found = false;
        for (VarInfo var2 : original.var_infos) {
          if (var.name().equals(var2.name())) {
            values[k] = vt.getValueOrNull(var2);
            mods[k] = vt.getModified(var2);
            found = true;
            break;
          }
        }

        if (!found) {
          values[k] = null;
          mods[k] = 2;
        }
        k++;
      }

      ValueTuple receiver_vt = new ValueTuple(values, mods);

      FileIO.compute_orig_variables(receiver, receiver_vt.vals, receiver_vt.mods, nonce);
      FileIO.compute_derived_variables(receiver, receiver_vt.vals, receiver_vt.mods);

      return receiver_vt;
    }

    /**
     * Process the sample by checking it against each existing invariant at the program point and
     * removing the invariant from the list of possibles if any invariant is falsified.
     */
    @Override
    public void process_sample(
        PptMap all_ppts, PptTopLevel ppt, ValueTuple vt, @Nullable Integer nonce) {
      this.all_ppts = all_ppts;

      // Add samples to orig and derived variables
      FileIO.compute_orig_variables(ppt, vt.vals, vt.mods, nonce);
      FileIO.compute_derived_variables(ppt, vt.vals, vt.mods);

      // Intern the sample
      vt = new ValueTuple(vt.vals, vt.mods);

      // DaikonSimple must make the object program point manually because
      // the new Chicory produced dtrace files do not contain object ppts
      // in the dtrace part of the file (the program point is declared).

      // Make the object ppt
      PptName ppt_name = ppt.ppt_name;

      PptTopLevel object_ppt = null;
      PptTopLevel class_ppt = null;
      ValueTuple object_vt = null;
      ValueTuple class_vt = null;

      if ((ppt_name.isEnterPoint() && !ppt_name.isConstructor()) || ppt_name.isExitPoint()) {
        object_ppt = all_ppts.get(ppt_name.makeObject());
        class_ppt = all_ppts.get(ppt_name.makeClassStatic());
      }

      // C programs do not have object ppts
      // check whether the ppt is a static or instance method
      // that decides whether the sample is copied over to the object and/or
      // class ppt
      if (object_ppt != null) {

        // the check assumes that static fields are not stored first in the
        // object ppt
        if (ppt.find_var_by_name(object_ppt.var_infos[0].name()) != null) {
          // object and class ppt should be created
          object_vt = copySample(object_ppt, ppt, vt, nonce);

          if (class_ppt != null) {
            class_vt = copySample(class_ppt, ppt, vt, nonce);
          }

        } else {
          // only class ppt should be created
          if (class_ppt != null) {
            class_vt = copySample(class_ppt, ppt, vt, nonce);
          }

          object_vt = null;
          object_ppt = null;
        }
      }

      // If this is an enter point, just remember it for later
      if (ppt_name.isEnterPoint()) {
        assert nonce != null;
        assert call_map.get(nonce) == null;
        List<Call> value = new ArrayList<>();
        value.add(new Call(ppt, vt));

        if (object_ppt != null) {
          value.add(new Call(object_ppt, object_vt));
        }

        if (class_ppt != null) {
          value.add(new Call(class_ppt, class_vt));
        }

        call_map.put(nonce, value);
        last_nonce = nonce;
        wait = true;
        return;
      }

      // If this is an exit point, process the saved enter (and sometimes
      // object) point
      if (ppt_name.isExitPoint()) {
        assert nonce != null;
        List<Call> value = call_map.remove(nonce);

        add(ppt, vt, nonce);

        for (Call ec : value) {
          add(ec.ppt, ec.vt, nonce);
        }
        wait = false;
      }

      if (object_ppt != null) add(object_ppt, object_vt, nonce); // apply object vt

      if (class_ppt != null) add(class_ppt, class_vt, nonce);
    }

    /**
     * The method iterates through all of the invariants in the ppt and manually adds the sample to
     * the invariant and removing the invariant if it is falsified.
     */
    private void add(PptTopLevel ppt, ValueTuple vt, int nonce) {

      List<PredValPair> row = new ArrayList<>();

      // if this is a numbered exit, apply to the combined exit as well
      if (ppt.ppt_name.isNumberedExitPoint()) {

        // Daikon.create_combined_exits(all_ppts);
        PptTopLevel parent = all_ppts.get(ppt.ppt_name.makeExit());
        if (parent != null) {
          parent.get_missingOutOfBounds(ppt, vt);
          add(parent, vt, nonce);

        } else {
          // make parent and apply

          // this is a hack. it should probably filter out orig and derived
          // vars instead of taking the first n.
          int len = ppt.num_tracevars + ppt.num_static_constant_vars;
          VarInfo[] exit_vars = new VarInfo[len];
          for (int j = 0; j < len; j++) {
            @SuppressWarnings("interning") // newly created, about to be used in a program point
            @Interned VarInfo exit_var = new VarInfo(ppt.var_infos[j]);
            exit_vars[j] = exit_var;
            exit_vars[j].varinfo_index = ppt.var_infos[j].varinfo_index;
            exit_vars[j].value_index = ppt.var_infos[j].value_index;
            exit_vars[j].equalitySet = null;
          }

          parent = new PptTopLevel(ppt.ppt_name.makeExit().getName(), exit_vars);
          Daikon.init_ppt(parent, all_ppts);
          all_ppts.add(parent);
          parent.get_missingOutOfBounds(ppt, vt);
          add(parent, vt, nonce);
        }
      }

      // ignore numbered exit poits
      if (ppt.ppt_name.isNumberedExitPoint()) {
        return;
      }

      // If the point has no variables, skip it
      if (ppt.var_infos.length == 0) {
        // The sample should be skipped but Daikon does not do this so
        // DaikonSimple will not do this to be consistent.
        // The better idea is for Daikon to assert that these valuetuples are
        // empty and then skip the sample.
        assert vt.size() == 0;
        return;
      }

      // Instantiate slices and invariants if this is the first sample
      if (ppt.num_samples() == 0) {
        instantiate_views_and_invariants(ppt);
      }

      // manually inc the sample number because DaikonSimple does not
      // use any of PptTopLevel's add methods which increase the sample
      // number
      ppt.incSampleNumber();

      // Loop through each slice
      for (PptSlice slice : ppt.views_iterable()) {
        Iterator<Invariant> k = slice.invs.iterator();
        boolean missing = false;

        for (VarInfo v : slice.var_infos) {
          // If any var has encountered out of array bounds values,
          // stop all invariants in this slice. The presumption here is that
          // an index out of bounds implies that the derived variable (eg a[i])
          // doesn't really make any sense (essentially that i is not a valid
          // index for a). Invariants on the derived variable are thus not
          // relevant.
          // If any variables are out of bounds, remove the invariants
          if (v.missingOutOfBounds()) {
            while (k.hasNext()) {
              Invariant inv = k.next();
              k.remove();
            }
            missing = true;
            break;
          }

          // If any variables are missing, skip this slice
          if (v.isMissing(vt)) {
            missing = true;
            break;
          }
        }

        // keep a list of the falsified invariants
        if (!missing) {
          while (k.hasNext()) {

            Invariant inv = k.next();
            Invariant pre_inv = inv.clone();
            for (VarInfo vi : inv.ppt.var_infos) {
              assert vt.getValue(vi) != null : vi;
            }
            if (inv.ppt instanceof PptSlice2) assert inv.ppt.var_infos.length == 2;
            InvariantStatus status = inv.add_sample(vt, 1);
            debug.fine(inv + ": " + status + " at " + ppt.name);
            if (status == InvariantStatus.FALSIFIED) {
              row.add(new PredValPair(inv, false));
              // k.remove();
            }
          }
        }

        // update num_samples and num_values of a slice manually
        // because DaikonSimple does not call any of PptTopLevel's
        // add methods
        for (int j = 0; j < vt.vals.length; j++) {
          if (!vt.isMissing(j)) {
            ValueSet vs = ppt.value_sets[j];
            vs.add(vt.vals[j]);
          }
        }
        ppt.mbtracker.add(vt, 1);
      }

      // write a row to a csv file
      try (CSVPrinter printer =
          new CSVPrinter(
              new FileWriter(new File(output_data_dir, ppt.csv_file_name), true),
              CSVFormat.DEFAULT)) {
        printer.printRecord(row);
      } catch (IOException e) {
        throw new Error("IO exception for " + output_data_dir + "/" + ppt.csv_file_name);
      }
    }
  }

  public static class InvIDManager {
    Map<Invariant, Integer> id_map = new LinkedHashMap<>();
    int last_id = 0;

    int getID(Invariant inv) {
      Integer id = id_map.get(inv);
      if (id != null) return id;

      id_map.put(inv, last_id);
      return last_id++;
    }
  }
}
