//============================================== TREE =====================================================================
var ZipNumber = -1;
var filesInZip = -1;
var RUN_TAB_INDEX = -1;
var FAULT_TAB_INDEX = -1;

function loadFile(fileName) {
    resetTabs();

    if (fileName == null || fileName === undefined || fileName.length == 0) {
        showNodeData(null);
        return;
    }
    var nodeData = null;
    //var chartDetailsUrl = 'bb.json'; //should be ID!!!
    if (ZipNumber > 0) {
        if (navigator.appName.indexOf("Explorer") > 0) {
            alert("File compression is not supported in Microsoft Internet Explorer. Please use Firefox or Chrome");
            return;
        }
        getJsonFile(fileName, getZipFileName(fileName));
    } else {
        $.ajax({
            type: "GET",
            url: fileName,
            contentType: "application/json; charset=utf-8",
            dataType: "json",
            success: function (data) {
                nodeData = data;


            },
            error: function (jqXHR) {
                alert(jqXHR.responseText);

            },
            complete: function () {
                showNodeData(nodeData);
            }


        });
    }
}


function getZipFileName(fn) {
    var res = "";
    var num = fn.substr("covData".length, (fn.indexOf(".json") - "covData".length));
    var n = parseInt(num, 10);
    if (n >= 0) {
        var b = parseInt(n / ZipNumber);
        //alert(b);
        ++b;
        res = "zipData" + b + ".zip";
    }
    return res;
}


function showDiv(id, isVisible) {
    if (document.getElementById(id) != null) {
        document.getElementById(id).style.visibility = isVisible ? 'visible' : 'hidden';
    }
}

function resetTabs() {
    if (isVplan) {
        diff_tab($("#instance_block_table"), -1, 1, false, 0);
        diff_tab($("#instance_expression_table"), -1, 1, false, 0);
        diff_tab($("#instance_toggle_table"), -1, 1, false, 0);
        diff_tab($("#instance_statement_table"), -1, 1, false, 0);
    }
    diff_tab($("#block_table"), -1, 1, false, 0);
    exprData = emptyData;
    diff_expression_tab();
    diff_tab($("#toggle_table"), -1, 1, false, 0);
    diff_tab($("#statement_table"), -1, 1, false, 0);
    diff_tab($("#assertion_table"), -1, 1, false, 0);
    diff_tab($("#fsm_table"), -1, 1, false, 0);
    diff_tab($("#cover_table"), -1, 1, false, 0);
    diff_tab($("#run_table"), -1, 1, false, 0);
    diff_tab($("#fault_table"), -1, 1, false, 0);


    diff_tab($("#fsm_state_table"), -1, 1, false, 0);
    diff_tab($("#fsm_transition_table"), -1, 1, false, 0);


    diff_tab($("#cover_item_table"), -1, 1, false, 0);
    diff_tab($("#cover_bin_table"), -1, 1, true, 0);

    showDiv('t1', false);
    showDiv('t2', false);
    showDiv("table_coverexpression_secondTable", false);
    showDiv('t3', false);
    showDiv('t4', false);
    showDiv('fsm_arc_table', false);// regular reset causes the render problem in arc table???

    diff_tab($("#run_error_table"), -1, 1, false, 0);
    diff_tab($("#run_warn_table"), -1, 1, false, 0);
    diff_tab($("#run_prop_table"), -1, 1, false, 0);

    //diff_tab($("#fault_prime_table"), -1, 1, false, 0);

    showLoadingTabs(true);

}

function showLoadingTabs(bShow) {
    document.getElementById('loadingTabs').style.visibility = bShow ? 'visible' : 'hidden';
    document.getElementById('tabs').style.visibility = bShow ? 'hidden' : 'visible';
}

function hideLoading() {
    document.getElementById('loadingTabs').style.visibility = 'hidden';
}


function addMouseDownEventHandler(table) {
    table.$container.on("mousedown", function (event, data) {

        document.getElementById('loadingTabs').style.visibility = 'visible';

    });
}


var BLOCK = 1;
var BLOCK_INSTANCE = 11;
var EXPRESSION = 2;
var SUB_EXPRESSION = 21;
var COVER_EXPRESSION = 22;
var PARITY_EXPRESSION = 23;
var EXPRESSION_INSTANCE = 24;
var COVER_EXPRESSION_SECOND_TABLE = 25;

var TOGGLES = 3;
var SIGNALS = 31;
var TOGGLE_INSTANCE = 32;

var STATEMENT = 4;
var STATEMENT_INSTANCE = 41;

var FSM = 5;
var FSM_STATE = 51;
var FSM_TRANSITION = 52;
var FSM_ARC = 523;

var COVER = 6;
var COVER_ITEM = 61;
var COVER_BIN = 611;

var ASSERTION = 7;

var RUN = 8;
var ERROR = 9;
var WARN = 10;
var PROP = 11;

var FAULT = 12;
var PRIME = 13;

var emptyData = [
    {"a": "  ", "title": "   ", "lazy": false, "folder": false}
];
var blockData = null;
var blockInstanceData = null;
var exprData = null;
var subExprData = null;
var coverExprData = null;
var coverExprDataTable2 = null;
var parityExprData = null;
var exprInstanceData = null;
var statementData = null;
var statementInstanceData = null;
var toggleData = null;
var signalData = null;
var toggleInstanceData = null;
var assertionData = null;
var fsmData = null;
var fsmStateData = null;
var fsmTransData = null;
var fsmArcData = null;
var coverData = null;
var coverItemData = null;
var coverBinData = null;
var runData = null;
var errorData = null;
var warnData = null;
var propData = null;
var faultData = null;
var primeData = null;

function showNodeData(nodeData) {

    if (nodeData == null || nodeData == undefined || nodeData.length == 0) {
        $("#tabs").tabs({disabled: true});
        showLoadingTabs(false);
        return;
    }

    $("#tabs").tabs({disabled: false});

    if (isVplan) {
        blockInstanceData = nodeData.block_instance_items;
        exprInstanceData = nodeData.expression_instance_items;
        toggleInstanceData = nodeData.toggle_instance_items;
        statementInstanceData = nodeData.statement_instance_items;
        runData = nodeData.run_items;
    } else {
        blockData = nodeData.block_items;
        exprData = nodeData.expression_items;
        toggleData = nodeData.toggle_items;
        statementData = nodeData.statement_items;
        faultData = nodeData.fault_items;
    }
    assertionData = nodeData.assertion_items;
    fsmData = nodeData.fsm_items;
    coverData = nodeData.cover_group_items;

    var disableTabs = [];
    if (isVplan === true) {
        if (blockInstanceData === undefined || blockInstanceData == null || blockInstanceData.length == 0) {
            blockInstanceData = null;
            if (BLOCK_TAB_INDEX >= 0) // $("#tabs").tabs({ disabled: [BLOCK_TAB_INDEX] });
            {
                disableTabs[disableTabs.length] = BLOCK_TAB_INDEX;
            }
        }
        if (exprInstanceData == null || exprInstanceData === undefined || exprInstanceData.length == 0) {
            exprInstanceData = null;
            if (EXPRESSION_TAB_INDEX >= 0) {
                disableTabs[disableTabs.length] = EXPRESSION_TAB_INDEX;
            }
        }
        if (toggleInstanceData == null || toggleInstanceData === undefined || toggleInstanceData.length == 0) {
            toggleInstanceData = null;
            if (TOGGLE_TAB_INDEX >= 0) {
                disableTabs[disableTabs.length] = TOGGLE_TAB_INDEX;
            }
        }
        if (statementInstanceData === undefined || statementInstanceData == null || statementInstanceData.length == 0) {
            statementInstanceData = null;
            if (STATEMENT_TAB_INDEX >= 0) {
                disableTabs[disableTabs.length] = STATEMENT_TAB_INDEX;
            }		//$("#tabs").tabs({ disabled: [STATEMENT_TAB_INDEX] });
        }

    } else {
        if (blockData === undefined || blockData == null || blockData.length == 0) {
            blockData = null;
            if (BLOCK_TAB_INDEX >= 0) // $("#tabs").tabs({ disabled: [BLOCK_TAB_INDEX] });
            {
                disableTabs[disableTabs.length] = BLOCK_TAB_INDEX;
            }
        }
        if (exprData == null || exprData === undefined || exprData.length == 0) {
            exprData = null;
            if (EXPRESSION_TAB_INDEX >= 0) {
                disableTabs[disableTabs.length] = EXPRESSION_TAB_INDEX;
            }
        }
        if (toggleData == null || toggleData === undefined || toggleData.length == 0) {
            toggleData = null;
            if (TOGGLE_TAB_INDEX >= 0) {
                disableTabs[disableTabs.length] = TOGGLE_TAB_INDEX;
            }
        }
        if (statementData === undefined || statementData == null || statementData.length == 0) {
            statementData = null;
            if (STATEMENT_TAB_INDEX >= 0) {
                disableTabs[disableTabs.length] = STATEMENT_TAB_INDEX;
            }		//$("#tabs").tabs({ disabled: [STATEMENT_TAB_INDEX] });
        }
    }


    if (fsmData === undefined || fsmData == null || fsmData.length == 0) {
        fsmData = null;
        if (FSM_TAB_INDEX >= 0) {
            disableTabs[disableTabs.length] = FSM_TAB_INDEX;
        }		//$("#tabs").tabs({ disabled: [STATEMENT_TAB_INDEX] });
    }
    if (coverData === undefined || coverData == null || coverData.length == 0) {
        coverData = null;
        if (COVER_TAB_INDEX >= 0) {
            disableTabs[disableTabs.length] = COVER_TAB_INDEX;
        }		//$("#tabs").tabs({ disabled: [STATEMENT_TAB_INDEX] });
    }
    if (assertionData === undefined || assertionData == null || assertionData.length == 0) {
        assertionData = null;
        if (ASSERTION_TAB_INDEX >= 0) {
            disableTabs[disableTabs.length] = ASSERTION_TAB_INDEX;
        }
    }

    if (runData === undefined || runData == null || runData.length == 0) {
        runData = null;
        if (RUN_TAB_INDEX != undefined && RUN_TAB_INDEX >= 0) {
            disableTabs[disableTabs.length] = RUN_TAB_INDEX;
        }
    }

    if (faultData === undefined || faultData == null || faultData.length == 0) {
        faultData = null;
        if (FAULT_TAB_INDEX != undefined && FAULT_TAB_INDEX >= 0) {
            disableTabs[disableTabs.length] = FAULT_TAB_INDEX;
        }
    }


    $("#tabs").tabs({disabled: disableTabs});

    if (isVplan === true) {
        if (blockInstanceData != null) {
            try {
                diff_tab($("#instance_block_table"), BLOCK_INSTANCE, instance_block_title_column_number, false, 0, instanceBlockItemSelectedAction);
            } catch (e) {
            }
        }
        if (exprInstanceData != null) {
            try {
                diff_tab($("#instance_expr_table"), EXPRESSION_INSTANCE, instance_expression_title_column_number, false, 0, instanceExprItemSelectedAction);
            } catch (e) {
            }
        }
        if (toggleInstanceData != null) {
            try {
                diff_tab($("#instance_toggle_table"), TOGGLE_INSTANCE, instance_signal_title_column_number, false, 0, instanceToggleItemSelectedAction);
            } catch (e) {
            }
        }
        if (statementInstanceData != null) {
            try {
                diff_tab($("#instance_statement_table"), STATEMENT_INSTANCE, instance_statement_table_title_column_number, false, 0, instanceStatementItemSelectedAction);
            } catch (e) {
            }
        }


    } else {
        if (blockData != null) {
            try {
                diff_tab($("#block_table"), BLOCK, -1, false, 0);
            } catch (e) {
            }
        }
        if (exprData != null) {
            try {
                diff_expression_tab(exprData);
            } catch (e) {
            }
        }
        if (toggleData != null) {
            try {
                diff_toggle_tab();//diff_tab($("#toggle_table"), TOGGLES, 1, false, 0);
            } catch (e) {
            }
        }
        if (statementData != null) {
            try {
                diff_tab($("#statement_table"), STATEMENT, -1, false, 0);
            } catch (e) {
            }
        }
    }
    if (fsmData != null) {
        try {
            diff_fsm_tab();//diff_tab($("#fsm_table"), FSM, -1, false, 0);
        } catch (e) {
        }
    }
    if (coverData != null) {
        try {
            diff_cover_tab();// diff_tab($("#cover_table"), COVER, -1, false, 0);
        } catch (e) {
        }
    }
    if (assertionData != null) {
        try {
            diff_tab($("#assertion_table"), ASSERTION, assertion_table_title_column_number, false, 0);
        } catch (e) {
        }
    }
    if (runData != null) {
        try {
            diff_run_tab();
        } catch (e) {
        }
    }
    if (faultData != null) {
        try {
            diff_tab($("#fault_table"), FAULT, fault_table_title_column_number, false, 0);// faultItemSelectedAction);
        } catch (e) {
        }
    }
    showLoadingTabs(false);
    selectCorrectTab(disableTabs);
}


function selectCorrectTab(disableTabs) {
    // Getter
    var activeTab = $("#tabs").tabs("option", "active");
    for (var i = 0; i < disableTabs.length; ++i) {
        if (disableTabs[i] == activeTab) {
            if (blockData != null)
                $("#tabs").tabs("option", "active", BLOCK_TAB_INDEX);
            else if (exprData != null)
                $("#tabs").tabs("option", "active", EXPRESSION_TAB_INDEX);
            else if (toggleData != null)
                $("#tabs").tabs("option", "active", TOGGLE_TAB_INDEX);
            else if (statementData != null)
                $("#tabs").tabs("option", "active", STATEMENT_TAB_INDEX);
            else if (fsmData != null)
                $("#tabs").tabs("option", "active", FSM_TAB_INDEX);
            else if (coverData != null)
                $("#tabs").tabs("option", "active", COVER_TAB_INDEX);
            else if (assertionData != null)
                $("#tabs").tabs("option", "active", ASSERTION_TAB_INDEX);
            else if (runData != null)
                $("#tabs").tabs("option", "active", RUN_TAB_INDEX);
            else if (faultData != null)
                $("#tabs").tabs("option", "active", FAULT_TAB_INDEX);
        }
    }

}


function getDataByType(type) {
    switch (type) {
        case BLOCK:
            return blockData == null ? emptyData : blockData;
        case BLOCK_INSTANCE:
            return blockInstanceData == null ? emptyData : blockInstanceData;
        case EXPRESSION:
            return exprData == null ? emptyData : exprData;
        case SUB_EXPRESSION:
            return subExprData == null ? emptyData : subExprData;
        case COVER_EXPRESSION:
            return coverExprData == null ? emptyData : coverExprData;
        case COVER_EXPRESSION_SECOND_TABLE:
            return coverExprDataTable2 == null ? emptyData : coverExprDataTable2;
        case PARITY_EXPRESSION:
            return parityExprData == null ? emptyData : parityExprData;
        case EXPRESSION_INSTANCE :
            return exprInstanceData == null ? emptyData : exprInstanceData;
        case TOGGLES:
            return toggleData == null ? emptyData : toggleData;
        case SIGNALS:
            return signalData == null ? emptyData : signalData;
        case TOGGLE_INSTANCE:
            return toggleInstanceData == null ? emptyData : toggleInstanceData;
        case STATEMENT:
            return statementData == null ? emptyData : statementData;
        case STATEMENT_INSTANCE:
            return statementInstanceData == null ? emptyData : statementInstanceData;
        case FSM:
            return fsmData == null ? emptyData : fsmData;
        case FSM_STATE:
            return fsmStateData == null ? emptyData : fsmStateData;
        case FSM_TRANSITION:
            return fsmTransData == null ? emptyData : fsmTransData;
        case FSM_ARC:
            return fsmArcData == null ? emptyData : fsmArcData;
        case COVER :
            return coverData == null ? emptyData : coverData;
        case COVER_ITEM:
            return coverItemData == null ? emptyData : coverItemData;
        case COVER_BIN:
            return coverBinData == null ? emptyData : coverBinData;
        case ASSERTION:
            return assertionData == null ? emptyData : assertionData;
        case RUN:
            return runData == null ? emptyData : runData;
        case ERROR:
            return errorData == null ? emptyData : errorData;
        case WARN:
            return warnData == null ? emptyData : warnData;
        case PROP:
            return propData == null ? emptyData : propData;
        case FAULT:
            return faultData == null ? emptyData : faultData;
        case PRIME:
            return primeData == null ? emptyData : primeData;
        default:
            return emptyData;
    }
}

var currentType = null;

function diff_tab(tab, dataType, title_index, isTerm, ident, actFunc) {
    currentType = dataType;
    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:
    //var isLoaded =false;
    tab.fancytree({
        extensions: ["table", "filter"],
        quicksearch: true,
        checkbox: false,
        filter: {
            mode: "hide",
            autoApply: true
        },
        debugLevel: 0,
        source: function () {
            return getDataByType(currentType);
        },
        activate: actFunc == undefined || actFunc == null ? function (event, data) {
            hideLoading();
        } : actFunc,

        lazyLoad: function (event, data) {
            if (filesInZip > 0) {

                showSubFolders(data.node.data.sub_items, data);
                data.result = [];

            } else {
                data.result = {url: data.node.data.sub_items};
            }
        },

        table: {
            indentation: ident,      // indent 20px per node level
            nodeColumnIdx: title_index   // render the node title into the 0nd column
            //checkboxColumnIdx: 0  // render the checkboxes into the 1st column
        },

        renderColumns: function (event, data) {
            getCell(event, data, title_index, isTerm);

        },
        postProcess: function (event, data) {

        },
        icons: false, // Display node icons.
        focusOnSelect: true

    });
}


//filter
//iplementFilter($("input[name=search2]"),  $("button#btnResetSearch2"), $("span#matches2"), tree_table2) ;


function diff(input) {

    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:

    $("#treetable").fancytree({
        extensions: ["table", "filter"],
        quicksearch: true,
        checkbox: false,
        selectMode: 1,
        debugLevel: 0,
        filter: {
            mode: "hide",
            autoApply: true
        },

        source: {
            url: input,
            cache: true
        },

        activate: function (event, data) {
            loadFile(data.node.data.cov_data);
        },

        lazyLoad: function (event, data) {
            if (filesInZip > 0) {
                showSubFolders(data.node.data.sub_items, data);
                data.result = [];
            } else {
                data.result = {url: data.node.data.sub_items};
            }
        },

        table: {
            indentation: 20,      // indent 20px per node level
            nodeColumnIdx: tree_table_name_column_index     // render the node title into the 0nd column
            //checkboxColumnIdx: 0  // render the checkboxes into the 1st column
        },

        renderColumns: function (event, data) {
            getCell(event, data, tree_table_name_column_index);

        },
        icons: false, // Display node icons.
        focusOnSelect: true,
        postProcess: function (event, data) {
            document.getElementById('treetable').style.display = 'block';
            document.getElementById('treetable').style.visibility = 'visible';
            document.getElementById('loading').innerHTML = "";
            document.getElementById('loading').style.visibility = 'hidden';
            resetTabs();
            showLoadingTabs(false);

        }
    });
    var tree_table = $("#treetable").fancytree("getTree");
    //filter
    implementFilter($("input[name=search]"), $("button#btnResetSearch"), $("span#matches"), tree_table);
    $("button#btnResetSearch").click();

}


//===========================================expression================================
function diff_expression_tab() {
    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:

    $("#expression_table").fancytree({
        extensions: ["table", "filter"],
        quicksearch: true,
        checkbox: false,
        selectMode: 1,
        debugLevel: 0,
        filter: {
            mode: "hide",
            autoApply: true
        },

        source: function () {
            return getDataByType(EXPRESSION);
        },

        activate: function (event, data) {
            showDiv('t1', false);
            showDiv('t2', false);
            showDiv('table_coverexpression_secondTable', false);
            subExprData = data.node.data.subitems === undefined ? emptyData : data.node.data.subitems;
            try {
                diff_subexpression_tab();
            } catch (e) {
            }
        },


        lazyLoad: function (event, data) {
            data.result = {url: "lazy.json"};
        },

        table: {
            indentation: 0,      // indent 20px per node level
            nodeColumnIdx: expression_table_title_column_number     // render the node title into the 0nd column
            //checkboxColumnIdx: 0  // render the checkboxes into the 1st column
        },

        renderColumns: function (event, data) {
            getCell(event, data, expression_table_title_column_number);

        },
        icons: false, // Display node icons.
        focusOnSelect: true
    });

    subExprData = emptyData;
    diff_subexpression_tab();
    showDiv('t1', false);
    showDiv('t2', false);
    showDiv("table_coverexpression_secondTable", false);
}


var expression_table = $("#table_expression").fancytree("getTree");
implementFilter($("input[name=search_expression]"), $("button#btnResetSearch_expression"), $("span#matches_expression"), expression_table);


function diff_subexpression_tab() {

    $("#subexpression_table").fancytree({
        extensions: ["table", "filter"],
        quicksearch: true,
        checkbox: false,
        selectMode: 1,
        debugLevel: 0,
        filter: {
            mode: "hide",
            autoApply: true
        },
        source: function () {
            return getDataByType(SUB_EXPRESSION);
        },
        activate: function (event, data) {


            if (data.node.data.subitems === undefined) {
                if (data.node.data.table_type === "parity") {
                    showDiv('t2', true);
                    showDiv('t1', false);
                    showDiv("table_coverexpression_secondTable", false);
                    try {
                        diff_tab($("#table_parityexpression"), -1, 1, false, 0);
                    } catch (e) {

                    }
                } else {
                    showDiv('t1', true);
                    showDiv('t2', false);
                    showDiv("table_coverexpression_secondTable", false);
                    try {
                        diff_tab($("#table_coverexpression"), -1, -1, false, 0);
                    } catch (e) {

                    }
                }


            } else {
                if (data.node.data.table_type === "parity") {

                    try {
                        parityExprData = data.node.data.subitems;
                        diff_tab($("#table_parityexpression"), PARITY_EXPRESSION, parity_expression_title_column_number, false, 10);
                    } catch (e) {

                    }
                    showDiv('t2', true);
                    showDiv('t1', false);
                    showDiv("table_coverexpression_secondTable", false);

                } else {
                    try {
                        var columnsStr = (data.node.data.columns == null || data.node.data.columns == undefined ? "" : data.node.data.columns);
                        var columnHeader = getTableFromStrs(columnsStr.split(';'));
                        document.getElementById('No attribute').innerHTML = columnHeader;


                        var subTitle = ( data.node.data.header == undefined || data.node.data.header == null ? "" : data.node.data.header);
                        document.getElementById('coverTableTitle').title = subTitle;


                        if (subTitle.length > 80) {
                            subTitle = subTitle.substr(0, 80) + "  ...";
                        }
                        var strTitle = "<b>" + ( data.node.data.cov_table_title == undefined || data.node.data.cov_table_title == null ? "Coverage Table" : data.node.data.cov_table_title ) + "</b>&nbsp;" + subTitle;

                        document.getElementById('coverTableTitle').innerHTML = strTitle;
                        coverExprData = data.node.data.subitems;
                        try {
                            diff_tab($("#table_coverexpression"), COVER_EXPRESSION, cover_expression_title_column_number, true, 0);
                        } catch (e) {
                        }


                        if (data.node.data.subitems1 == undefined) {
                            diff_tab($("#table_coverexpression_secondTable"), null, -1, false, 0);
                            showDiv("table_coverexpression_secondTable", false);
                        } else {
                            coverExprDataTable2 = data.node.data.subitems1;
                            try {
                                diff_tab($("#table_coverexpression_secondTable"), COVER_EXPRESSION_SECOND_TABLE, cover_expression_title_column_number, true, 0);
                            } catch (e) {
                            }
                            showDiv("table_coverexpression_secondTable", true);
                        }

                    } catch (e) {

                    }
                    showDiv('t2', false);
                    showDiv('t1', true);
                }

            }


        },


        lazyLoad: function (event, data) {
            data.result = {url: "lazy.json"};
        },

        table: {
            indentation: 0,      // indent 20px per node level
            nodeColumnIdx: sub_expression_title_column_number     // render the node title into the 0nd column
            //checkboxColumnIdx: 0  // render the checkboxes into the 1st column
        },

        renderColumns: function (event, data) {
            getCell(event, data, sub_expression_title_column_number);

        },
        icons: false, // Display node icons.
        focusOnSelect: true,
        postProcess: function (event, data) {
            showDiv('t2', false);
            showDiv('t1', false);
            showDiv("table_coverexpression_secondTable", false);
        }
    });


}


//======================================  TOGGLES ===================================================================

function diff_toggle_tab(input) {

    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:
    diff_tab($("#toggle_table"), TOGGLES, toggle_title_column_number, false, 0, toggleSelectedAction);
    var togle_table = $("#toggle_table").fancytree("getTree");
    //filter
    implementFilter($("input[name=toggle_search1]"), $("button#toggle_btnResetSearch1"), $("span#toggle_matches1"), togle_table);

    showDiv('t3', false);
    showDiv('t4', false);

}

function toggleSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#table_reg_signal"), null, -1, false, 0);
        showDiv('t3', true);
        showDiv('t4', false);
    } else {
        signalData = data.node.data.subitems;
        if (data.node.data.table_type === "reg") {
            try {
                diff_tab($("#table_reg_signal"), SIGNALS, signal_bit_title_column_number, false, 0);
                var togle_reg_table = $("#table_reg_signal").fancytree("getTree");
                //filter
                implementFilter($("input[name=toggle_search2]"), $("button#toggle_btnResetSearch2"), $("span#toggle_matches2"), togle_reg_table);

            } catch (e) {

            }
            showDiv('t3', true);
            showDiv('t4', false);

        } else {
            try {
                diff_tab($("#table_enum_signal"), SIGNALS, signal_bit_enum_title_column_number, false, 0);
                var togle_enum_table = $("#table_enum_signal").fancytree("getTree");
                //filter
                implementFilter($("input[name=toggle_search3]"), $("button#toggle_btnResetSearch3"), $("span#toggle_matches3"), togle_enum_table);
            } catch (e) {

            }
            showDiv('t3', false);
            showDiv('t4', true);
        }

    }
}

//======================================  FSM ===================================================================

function diff_fsm_tab() {

    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:
    diff_tab($("#fsm_table"), FSM, fsm_table_title_column_number, false, 0, fsmSelectedAction);
    var fsm_table = $("#fsm_table").fancytree("getTree");
    //filter
    implementFilter($("input[name=fsm_search]"), $("button#fsm_btnResetSearch"), $("span#fsm_matches"), fsm_table);
    showDiv('fsm_arc_table', false);

}

function fsmSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#fsm_state_table"), null, -1, false, 0);

    } else {
        fsmStateData = data.node.data.subitems;
        try {
            diff_tab($("#fsm_state_table"), FSM_STATE, state_table_title_column_number, false, 0);
            var fsm_state_table = $("#fsm_state_table").fancytree("getTree");
            //filter
            implementFilter($("input[name=fsm_search2]"), $("button#fsm_btnResetSearch2"), $("span#fsm_matches2"), fsm_state_table);
        } catch (e) {

        }

    }

    if (data.node.data.subitems1 === undefined) {
        diff_tab($("#fsm_transition_table"), null, -1, false, 0);

    } else {
        fsmTransData = data.node.data.subitems1;
        try {
            diff_tab($("#fsm_transition_table"), FSM_TRANSITION, transition_table_title_column_number, false, 0, transitionSelectedAction);
            var fsm_transition_table = $("#fsm_transition_table").fancytree("getTree");
            //filter
            implementFilter($("input[name=fsm_search2]"), $("button#fsm_btnResetSearch3"), $("span#fsm_matches3"), fsm_transition_table);
        } catch (e) {

        }

    }

    document.getElementById('fsm_arc_table').style.visibility = 'hidden';

}

function transitionSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#fsm_arc_table"), null, -1, false, 0);
        document.getElementById('fsm_arc_table').style.visibility = 'hidden';

    } else {
        fsmArcData = data.node.data.subitems;
        try {
            diff_arc_table()
        } catch (e) {

        }
        //document.getElementById('fsm_arc_table').style.visibility = 'visible';
    }


}


var inputName = null;
var inputDelimiter = " | ";

function diff_arc_table() {
    inputName = null;
    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:
    try {
        $("#fsm_arc_table").fancytree({
            extensions: ["table", "filter"],
            quicksearch: true,
            checkbox: false,
            filter: {
                mode: "hide",
                autoApply: true
            },
            source: function () {
                return getDataByType(FSM_ARC);
            },

            lazyLoad: function (event, data) {
                data.result = {url: "lazy.json"};
            },

            table: {
                indentation: 0,      // indent 20px per node level
                nodeColumnIdx: arc_table_title_column_number   // render the node title into the 0nd column
                //checkboxColumnIdx: 0  // render the checkboxes into the 1st column
            },

            renderColumns: function (event, data) {
                getCell(event, data, arc_table_title_column_number, true);

                if (inputName == null) {
                    inputName = data.node.data["input_title"];
                    document.getElementById('Input Signal Names').innerHTML = inputName == null ? "Inputs" : getTableFromStrs(inputName.split(';'));

                }

            },
            postProcess: function (event, data) {
                document.getElementById('fsm_arc_table').style.visibility = 'visible';

            },
            icons: false, // Display node icons.
            focusOnSelect: true

        });
    } catch (e) {

    }
    document.getElementById('fsm_arc_table').style.visibility = 'visible';

}

//================================== COVER GROUP=================================================
function diff_cover_tab() {

    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:
    diff_tab($("#cover_table"), COVER, cover_group_table_title_column_number, false, 0, coverGroupSelectedAction);
    var cover_table = $("#cover_table").fancytree("getTree");
    //filter
    implementFilter($("input[name=cover_search1]"), $("button#cover_btnResetSearch1"), $("span#cover_matches1"), cover_table);

}

function coverGroupSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#cover_item_table"), null, -1, false, 0);

    } else {
        coverItemData = data.node.data.subitems;
        data.node.isSelected()
        try {
            diff_tab($("#cover_item_table"), COVER_ITEM, item_table_title_column_number, false, 0, coverItemSelectedAction);
            var table = $("#cover_item_table").fancytree("getTree");
            addMouseDownEventHandler(table);
            //filter
            implementFilter($("input[name=cover_search2]"), $("button#cover_btnResetSearch2"), $("span#cover_matches2"), table);

        } catch (e) {

        }

    }
    diff_tab($("#cover_bin_table"), null, -1, false, 0);

}

function coverItemSelectedAction(event, data) {

    var columnsStr = (data.node.data.columns == null || data.node.data.columns == undefined ? "" : data.node.data.columns);
    if (columnsStr.length > 0) {
        var columnHeader = getTableFromStrs(columnsStr.split(';'));
        document.getElementById('Name_bin').innerHTML = columnHeader;
    } else {
        document.getElementById('Name_bin').innerHTML = "Name";
    }
    if (data.node.data.subitems === undefined) {
        diff_tab($("#cover_bin_table"), null, -1, false, 0);

    } else {
        coverBinData = data.node.data.subitems;
        try {
            diff_tab($("#cover_bin_table"), COVER_BIN, bin_table_title_column_number, true, 0, null);
            var table = $("#cover_bin_table").fancytree("getTree");
            //filter
            implementFilter($("input[name=cover_search3]"), $("button#cover_btnResetSearch3"), $("span#cover_matches3"), table);
        } catch (e) {
            alert(e)
        }

    }

    hideLoading();
}


function instanceBlockItemSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#block_table"), null, -1, false, 0);

    } else {
        blockData = data.node.data.subitems;
        try {
            diff_tab($("#block_table"), BLOCK, -1, false, 0);

        } catch (e) {

        }

    }


}

function instanceToggleItemSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#toggle_table"), null, -1, false, 0);

    } else {
        toggleData = data.node.data.subitems;
        try {
            diff_toggle_tab();

        } catch (e) {

        }

    }


}

function instanceExprItemSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#toggle_table"), null, -1, false, 0);

    } else {
        exprData = data.node.data.subitems;
        try {
            diff_expression_tab();

        } catch (e) {

        }

    }


}

function instanceStatementItemSelectedAction(event, data) {

    if (data.node.data.subitems === undefined) {
        diff_tab($("#statement_table"), null, -1, false, 0);

    } else {
        statementData = data.node.data.subitems;
        try {
            diff_tab($("#statement_table"), STATEMENT, -1, false, 0);

        } catch (e) {

        }

    }


}

function diff_run_tab() {

    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:
    diff_tab($("#run_table"), RUN, run_table_title_column_number, false, 0, runItemSelectedAction);
    var run_table = $("#run_table").fancytree("getTree");
    //filter
    implementFilter($("input[name=run_search]"), $("button#run_btnResetSearch"), $("span#run_matches"), run_table);
    $("button#run_btnResetSearch").click();

}


function runItemSelectedAction(event, data) {

    if (data.node.data.errors_items === undefined) {
        diff_tab($("#run_error_table"), null, -1, false, 0);
    }
    if (data.node.data.warn_items === undefined) {
        diff_tab($("#run_warn_table"), null, -1, false, 0);
    }
    if (data.node.data.properties_items === undefined) {
        diff_tab($("#run_prop_table"), null, -1, false, 0);
    } else {
        errorData = data.node.data.errors_items;
        warnData = data.node.data.warn_items;
        propData = data.node.data.properties_items;
        try {
            diff_tab($("#run_error_table"), ERROR, error_table_title_column_number, false, 0);
            var error_table = $("#run_error_table").fancytree("getTree");
            //filter
            implementFilter($("input[name=run_search_error]"), $("button#run_btnResetSearch_error"), $("span#run_matches_error"), error_table);
            diff_tab($("#run_warn_table"), WARN, warn_table_title_column_number, false, 0);
            var warn_table = $("#run_warn_table").fancytree("getTree");
            //filter
            implementFilter($("input[name=run_search_warn]"), $("button#run_btnResetSearch_warn"), $("span#run_matches_warn"), warn_table);
            diff_tab($("#run_prop_table"), PROP, prop_table_title_column_number, false, 0);
            //var prop_table = $("#prop_table").fancytree("getTree");
            //filter
            //implementFilter($("input[name=search_prop]"), $("button#btnResetSearch_prop"), $("span#matches_prop"), prop_table);

        } catch (e) {

        }

    }


}


function faultItemSelectedAction(event, data) {

    if (data.node.data.prime_items === undefined) {
        diff_tab($("#fault_prime_table"), null, -1, false, 0);
    } else {
        primeData = data.node.data.prime_items;
        try {
            diff_tab($("#fault_prime_table"), PRIME, fault_table_title_column_number, false, 0);
        } catch (e) {

        }

    }


}
