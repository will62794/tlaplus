package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormText;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableOverridesSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Represent all advanced model elements
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AdvancedModelPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaults
{

    public static final String ID = "advancedModelPage";

    private SourceViewer constraintSource;
    private SourceViewer actionConstraintSource;
    private SourceViewer newDefinitionsSource;
    private SourceViewer viewSource;
    private SourceViewer modelValuesSource;
    private Button dfidOption;
    private Button mcOption;
    private Button simulationOption;
    private Text dfidDepthText;
    private Text simuDepthText;
    private Text simuSeedText;
    private Text simuArilText;
    private TableViewer definitionsTable;

    /**
     * Constructs the page
     * @param editor
     */
    public AdvancedModelPage(FormEditor editor)
    {
        super(editor, AdvancedModelPage.ID, "Advanced Options");
        this.helpId = IHelpConstants.ADVANCED_MODEL_PAGE;
        this.imagePath = "icons/full/choice_sc_obj.gif";
    }

    /**
     * Loads data from the model
     */
    protected void loadData() throws CoreException
    {
        // definition overrides
        List definitions = getConfig().getAttribute(MODEL_PARAMETER_DEFINITIONS, new Vector());
        FormHelper.setSerializedInput(definitionsTable, definitions);

        // new definitions
        String newDefinitions = getConfig().getAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, EMPTY_STRING);
        newDefinitionsSource.setDocument(new Document(newDefinitions));

        // advanced model values
        String modelValues = getConfig().getAttribute(MODEL_PARAMETER_MODEL_VALUES, EMPTY_STRING);
        modelValuesSource.setDocument(new Document(modelValues));

        // constraint
        String constraint = getConfig().getAttribute(MODEL_PARAMETER_CONSTRAINT, EMPTY_STRING);
        constraintSource.setDocument(new Document(constraint));

        // view
        String view = getConfig().getAttribute(LAUNCH_VIEW, EMPTY_STRING);
        viewSource.setDocument(new Document(view));

        // action constraint
        String actionConstraint = getConfig().getAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, EMPTY_STRING);
        actionConstraintSource.setDocument(new Document(actionConstraint));

        // run mode mode
        boolean isMCMode = getConfig().getAttribute(LAUNCH_MC_MODE, LAUNCH_MC_MODE_DEFAULT);
        mcOption.setSelection(isMCMode);
        simulationOption.setSelection(!isMCMode);

        // DFID mode
        boolean isDFIDMode = getConfig().getAttribute(LAUNCH_DFID_MODE, LAUNCH_DFID_MODE_DEFAULT);
        dfidOption.setSelection(isDFIDMode);

        // DFID depth
        int dfidDepth = getConfig().getAttribute(LAUNCH_DFID_DEPTH, LAUNCH_DFID_DEPTH_DEFAULT);
        dfidDepthText.setText("" + dfidDepth);

        // simulation depth
        int simuDepth = getConfig().getAttribute(LAUNCH_SIMU_DEPTH, LAUNCH_SIMU_DEPTH_DEFAULT);
        simuDepthText.setText("" + simuDepth);

        // simulation aril
        int simuAril = getConfig().getAttribute(LAUNCH_SIMU_SEED, LAUNCH_SIMU_ARIL_DEFAULT);
        if (LAUNCH_SIMU_ARIL_DEFAULT != simuAril)
        {
            simuArilText.setText("" + simuAril);
        } else
        {
            simuArilText.setText("");
        }

        // simulation seed
        int simuSeed = getConfig().getAttribute(LAUNCH_SIMU_ARIL, LAUNCH_SIMU_SEED_DEFAULT);
        if (LAUNCH_SIMU_SEED_DEFAULT != simuSeed)
        {
            simuSeedText.setText("" + simuSeed);
        } else
        {
            simuSeedText.setText("");
        }
    }

    /**
     * Save data back to config
     */
    public void commit(boolean onSave)
    {
        System.out.println("Advanced page commit");

        boolean isMCMode = mcOption.getSelection();
        getConfig().setAttribute(LAUNCH_MC_MODE, isMCMode);

        // DFID mode
        boolean isDFIDMode = dfidOption.getSelection();
        getConfig().setAttribute(LAUNCH_DFID_MODE, isDFIDMode);

        int dfidDepth = Integer.parseInt(dfidDepthText.getText());
        int simuDepth = Integer.parseInt(simuDepthText.getText());
        int simuAril = LAUNCH_SIMU_ARIL_DEFAULT;
        int simuSeed = LAUNCH_SIMU_SEED_DEFAULT;

        if (!"".equals(simuArilText.getText()))
        {
            simuAril = Integer.parseInt(simuArilText.getText());
        }
        if (!"".equals(simuSeedText.getText()))
        {
            simuSeed = Integer.parseInt(simuSeedText.getText());
        }

        // DFID depth
        getConfig().setAttribute(LAUNCH_DFID_DEPTH, dfidDepth);
        // simulation depth
        getConfig().setAttribute(LAUNCH_SIMU_DEPTH, simuDepth);
        // simulation aril
        getConfig().setAttribute(LAUNCH_SIMU_SEED, simuSeed);
        // simulation seed
        getConfig().setAttribute(LAUNCH_SIMU_ARIL, simuAril);

        // definitions
        List definitions = FormHelper.getSerializedInput(definitionsTable);
        getConfig().setAttribute(MODEL_PARAMETER_DEFINITIONS, definitions);

        // new definitions
        String newDefinitions = FormHelper.trimTrailingSpaces(newDefinitionsSource.getDocument().get());
        getConfig().setAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, newDefinitions);

        // model values
        String modelValues = FormHelper.trimTrailingSpaces(modelValuesSource.getDocument().get());
        TypedSet modelValuesSet = TypedSet.parseSet(modelValues);
        getConfig().setAttribute(MODEL_PARAMETER_MODEL_VALUES, modelValuesSet.toString());

        // constraint formula
        String constraintFormula = FormHelper.trimTrailingSpaces(constraintSource.getDocument().get());
        getConfig().setAttribute(MODEL_PARAMETER_CONSTRAINT, constraintFormula);

        // view
        String viewFormula = FormHelper.trimTrailingSpaces(viewSource.getDocument().get());
        getConfig().setAttribute(LAUNCH_VIEW, viewFormula);

        // action constraint formula
        String actionConstraintFormula = FormHelper.trimTrailingSpaces(actionConstraintSource.getDocument().get());
        getConfig().setAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, actionConstraintFormula);

        super.commit(onSave);
    }

    /**
     * 
     */
    public void validate()
    {
        if (getManagedForm() == null)
        {
            return;
        }
        IMessageManager mm = getManagedForm().getMessageManager();
        mm.setAutoUpdate(false);

        // clean old messages
        mm.removeAllMessages();
        // make the run possible
        setComplete(true);

        // setup the names from the current page
        getLookupHelper().resetModelNames(this);

        try
        {
            int dfidDepth = Integer.parseInt(dfidDepthText.getText());
            if (dfidDepth <= 0)
            {
                mm.addMessage("dfid1", "Depth of DFID launch must be a positive integer", null, IMessageProvider.ERROR,
                        dfidDepthText);
                setComplete(false);
                expandSection(SEC_LAUNCHING_SETUP);
            }
        } catch (NumberFormatException e)
        {
            mm.addMessage("dfid2", "Depth of DFID launch must be a positive integer", null, IMessageProvider.ERROR,
                    dfidDepthText);
            setComplete(false);
            expandSection(SEC_LAUNCHING_SETUP);
        }
        try
        {
            int simuDepth = Integer.parseInt(simuDepthText.getText());
            if (simuDepth <= 0)
            {
                mm.addMessage("simuDepth1", "Length of the simulation tracemust be a positive integer", null,
                        IMessageProvider.ERROR, simuDepthText);
                setComplete(false);
                expandSection(SEC_LAUNCHING_SETUP);
            }

        } catch (NumberFormatException e)
        {
            mm.addMessage("simuDepth2", "Length of the simulation trace must be a positive integer", null,
                    IMessageProvider.ERROR, simuDepthText);
            setComplete(false);
            expandSection(SEC_LAUNCHING_SETUP);
        }
        if (!EMPTY_STRING.equals(simuArilText.getText()))
        {
            try
            {
                long simuAril = Long.parseLong(simuArilText.getText());
                if (simuAril <= 0)
                {
                    mm.addMessage("simuAril1", "The simulation aril must be a positive integer", null,
                            IMessageProvider.ERROR, simuArilText);
                    setComplete(false);
                }
            } catch (NumberFormatException e)
            {
                mm.addMessage("simuAril2", "The simulation aril must be a positive integer", null,
                        IMessageProvider.ERROR, simuArilText);
                setComplete(false);
                expandSection(SEC_LAUNCHING_SETUP);
            }
        }
        if (!EMPTY_STRING.equals(simuSeedText.getText()))
        {
            try
            {
                // long simuSeed =
                Long.parseLong(simuSeedText.getText());

            } catch (NumberFormatException e)
            {
                mm.addMessage("simuSeed1", "The simulation aril must be a positive integer", null,
                        IMessageProvider.ERROR, simuSeedText);
                expandSection(SEC_LAUNCHING_SETUP);
                setComplete(false);
            }
        }

        // check the model values
        TypedSet modelValuesSet = TypedSet.parseSet(FormHelper
                .trimTrailingSpaces(modelValuesSource.getDocument().get()));
        if (modelValuesSet.getValueCount() > 0)
        {
            // there were values defined

            // check if those are numbers?
            /*
            if (modelValuesSet.hasANumberOnlyValue())
            {
                mm.addMessage("modelValues1", "A model value can not be an number", modelValuesSet,
                        IMessageProvider.ERROR, modelValuesSource.getControl());
                setComplete(false);
            }*/
            List values = modelValuesSet.getValuesAsList();
            // check list of model values if these are already used
            validateUsage(MODEL_PARAMETER_MODEL_VALUES, values, "modelValues2_", "A model value",
                    "Advanced Model Values");
            // check whether the model values are valid ids
            validateId(MODEL_PARAMETER_MODEL_VALUES, values, "modelValues2_", "A model value");

            // get data binding manager and widget for model values
            DataBindingManager dm = getDataBindingManager();
            Control widget = UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_MODEL_VALUES));

            // check if model values are config file keywords
            for (int j = 0; j < values.size(); j++)
            {
                String value = (String) values.get(j);
                if (SemanticHelper.isConfigFileKeyword(value))
                {
                    mm.addMessage(value, "The toolbox cannot handle the identifier " + value + ".", null,
                            IMessageProvider.ERROR, widget);
                }
            }

        }

        // check the definition overrides
        List definitions = (List) definitionsTable.getInput();
        for (int i = 0; i < definitions.size(); i++)
        {
            Assignment definition = (Assignment) definitions.get(i);
            List values = Arrays.asList(definition.getParams());
            // check list of parameters
            validateUsage(MODEL_PARAMETER_DEFINITIONS, values, "param1_", "A parameter name", "Definition Overrides");
            // check whether the parameters are valid ids
            validateId(MODEL_PARAMETER_DEFINITIONS, values, "param1_", "A parameter name");
        }

        mm.setAutoUpdate(true);

        super.validate();
    }

    /**
     * Creates the UI
     */
    protected void createBodyContent(IManagedForm managedForm)
    {

        DataBindingManager dm = getDataBindingManager();
        int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE;

        FormToolkit toolkit = managedForm.getToolkit();
        Composite body = managedForm.getForm().getBody();

        GridData gd;
        TableWrapData twd;

        // left
        Composite left = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        left.setLayout(new GridLayout(1, false));
        left.setLayoutData(twd);

        // right
        Composite right = toolkit.createComposite(body);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        right.setLayoutData(twd);
        right.setLayout(new GridLayout(1, false));

        Section section;

        // ---------------------------------------------------------------
        // new definitions

        section = FormHelper
                .createSectionComposite(
                        left,
                        "Additional Definitions",
                        "Definitions required for the model checking, in addition to the definitions in the specificatoin modules.",
                        toolkit, sectionFlags, getExpansionListener());
        ValidateableSectionPart newDefinitionsPart = new ValidateableSectionPart(section, this, SEC_NEW_DEFINITION);
        managedForm.addPart(newDefinitionsPart);
        DirtyMarkingListener newDefinitionsListener = new DirtyMarkingListener(newDefinitionsPart, true);

        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 3;
        section.setLayoutData(gd);

        Composite newDefinitionsArea = (Composite) section.getClient();
        newDefinitionsSource = FormHelper.createFormsSourceViewer(toolkit, newDefinitionsArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        newDefinitionsSource.getTextWidget().setLayoutData(twd);
        newDefinitionsSource.addTextListener(newDefinitionsListener);

        dm.bindAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, newDefinitionsSource, newDefinitionsPart);

        // ---------------------------------------------------------------
        // definition overwrite

        ValidateableOverridesSectionPart definitionsPart = new ValidateableOverridesSectionPart(right,
                "Definition Override", "Replacement of operators and functions defined in specification modules.",
                toolkit, sectionFlags, this);

        managedForm.addPart(definitionsPart);
        // layout
        gd = new GridData(GridData.FILL_HORIZONTAL);
        definitionsPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_BOTH);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        definitionsPart.getTableViewer().getTable().setLayoutData(gd);
        definitionsTable = definitionsPart.getTableViewer();
        dm.bindAttribute(MODEL_PARAMETER_DEFINITIONS, definitionsTable, definitionsPart);

        // ---------------------------------------------------------------
        // constraint
        section = FormHelper.createSectionComposite(left, "State Constraint",
                "A state constraint is a formula restricting the possible states by a state predicate.", toolkit,
                sectionFlags, getExpansionListener());
        ValidateableSectionPart constraintPart = new ValidateableSectionPart(section, this, SEC_STATE_CONSTRAINT);
        managedForm.addPart(constraintPart);
        DirtyMarkingListener constraintListener = new DirtyMarkingListener(constraintPart, true);

        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 3;
        section.setLayoutData(gd);

        Composite constraintArea = (Composite) section.getClient();
        constraintSource = FormHelper.createFormsSourceViewer(toolkit, constraintArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        constraintSource.getTextWidget().setLayoutData(twd);
        constraintSource.addTextListener(constraintListener);
        dm.bindAttribute(MODEL_PARAMETER_CONSTRAINT, constraintSource, constraintPart);

        // ---------------------------------------------------------------
        // action constraint
        section = FormHelper.createSectionComposite(right, "Action Constraint",
                "An action constraint is a formula restricting the possible transitions.", toolkit, sectionFlags,
                getExpansionListener());
        ValidateableSectionPart actionConstraintPart = new ValidateableSectionPart(section, this, SEC_ACTION_CONSTRAINT);
        managedForm.addPart(actionConstraintPart);
        DirtyMarkingListener actionConstraintListener = new DirtyMarkingListener(actionConstraintPart, true);

        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 3;
        section.setLayoutData(gd);

        Composite actionConstraintArea = (Composite) section.getClient();
        actionConstraintSource = FormHelper.createFormsSourceViewer(toolkit, actionConstraintArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        actionConstraintSource.getTextWidget().setLayoutData(twd);
        actionConstraintSource.addTextListener(actionConstraintListener);
        dm.bindAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, actionConstraintSource, actionConstraintPart);

        // ---------------------------------------------------------------
        // modelValues
        section = FormHelper.createSectionComposite(left, "Model Values", "An additional set of model values.",
                toolkit, sectionFlags, getExpansionListener());
        ValidateableSectionPart modelValuesPart = new ValidateableSectionPart(section, this, SEC_MODEL_VALUES);
        managedForm.addPart(modelValuesPart);
        DirtyMarkingListener modelValuesListener = new DirtyMarkingListener(modelValuesPart, true);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 3;
        section.setLayoutData(gd);

        Composite modelValueArea = (Composite) section.getClient();
        modelValuesSource = FormHelper.createFormsSourceViewer(toolkit, modelValueArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        modelValuesSource.getTextWidget().setLayoutData(twd);
        modelValuesSource.addTextListener(modelValuesListener);
        dm.bindAttribute(MODEL_PARAMETER_MODEL_VALUES, modelValuesSource, modelValuesPart);

        // ---------------------------------------------------------------
        // launch
        section = createAdvancedLaunchSection(toolkit, right, sectionFlags);
        ValidateableSectionPart launchPart = new ValidateableSectionPart(section, this, SEC_LAUNCHING_SETUP);
        managedForm.addPart(launchPart);
        DirtyMarkingListener launchListener = new DirtyMarkingListener(launchPart, true);

        // dirty listeners
        simuArilText.addModifyListener(launchListener);
        simuSeedText.addModifyListener(launchListener);
        simuDepthText.addModifyListener(launchListener);
        dfidDepthText.addModifyListener(launchListener);
        simulationOption.addSelectionListener(launchListener);
        dfidOption.addSelectionListener(launchListener);
        mcOption.addSelectionListener(launchListener);
        viewSource.addTextListener(launchListener);

        // add section ignoring listeners
        dirtyPartListeners.add(newDefinitionsListener);
        dirtyPartListeners.add(actionConstraintListener);
        dirtyPartListeners.add(modelValuesListener);
        dirtyPartListeners.add(constraintListener);
        dirtyPartListeners.add(launchListener);
    }

    /**
     * @param toolkit
     * @param parent
     * @param flags
     */
    private Section createAdvancedLaunchSection(FormToolkit toolkit, Composite parent, int sectionFlags)
    {
        GridData gd;

        // advanced section
        Section advancedSection = FormHelper.createSectionComposite(parent, "Launching Setup",
                "Advanced settings of the TLC model checker", toolkit, sectionFlags, getExpansionListener());
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        gd.grabExcessHorizontalSpace = true;
        advancedSection.setLayoutData(gd);

        Composite area = (Composite) advancedSection.getClient();
        area.setLayout(new GridLayout(2, false));

        mcOption = toolkit.createButton(area, "Model-checking mode", SWT.RADIO);
        gd = new GridData();
        gd.horizontalSpan = 2;
        mcOption.setLayoutData(gd);

        // label view
        FormText viewLabel = toolkit.createFormText(area, true);
        viewLabel.setText("View:", false, false);
        gd = new GridData();
        gd.verticalAlignment = SWT.BEGINNING;
        gd.horizontalIndent = 10;
        viewLabel.setLayoutData(gd);
        // field view
        viewSource = FormHelper.createFormsSourceViewer(toolkit, area, SWT.V_SCROLL);
        // layout of the source viewer
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.grabExcessHorizontalSpace = true;
        gd.heightHint = 60;
        gd.widthHint = 200;
        viewSource.getTextWidget().setLayoutData(gd);

        dfidOption = toolkit.createButton(area, "Depth-first", SWT.CHECK);
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.horizontalIndent = 10;
        dfidOption.setLayoutData(gd);
        // label depth
        FormText dfidDepthLabel = toolkit.createFormText(area, true);
        dfidDepthLabel.setText("Depth:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        dfidDepthLabel.setLayoutData(gd);
        // field depth
        dfidDepthText = toolkit.createText(area, "100");
        gd = new GridData();
        gd.widthHint = 100;
        dfidDepthText.setLayoutData(gd);

        simulationOption = toolkit.createButton(area, "Simulation mode", SWT.RADIO);
        gd = new GridData();
        gd.horizontalSpan = 2;
        simulationOption.setLayoutData(gd);

        // label depth
        FormText depthLabel = toolkit.createFormText(area, true);
        depthLabel.setText("Maximum length of the trace:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        depthLabel.setLayoutData(gd);
        // field depth
        simuDepthText = toolkit.createText(area, "100");
        gd = new GridData();
        gd.widthHint = 100;
        simuDepthText.setLayoutData(gd);

        // label seed
        FormText seedLabel = toolkit.createFormText(area, true);
        seedLabel.setText("Seed:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        seedLabel.setLayoutData(gd);

        // field seed
        simuSeedText = toolkit.createText(area, "");
        gd = new GridData();
        gd.widthHint = 200;
        simuSeedText.setLayoutData(gd);

        // label seed
        FormText arilLabel = toolkit.createFormText(area, true);
        arilLabel.setText("Aril:", false, false);
        gd = new GridData();
        gd.horizontalIndent = 10;
        arilLabel.setLayoutData(gd);

        // field seed
        simuArilText = toolkit.createText(area, "");
        gd = new GridData();
        gd.widthHint = 200;
        simuArilText.setLayoutData(gd);

        return advancedSection;
    }
}
