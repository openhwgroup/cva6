function loadFile(fileName) {

    resetRun();
    showLoadingData(true);
    if (fileName == null || fileName === undefined || fileName.length == 0) {
        showNodeData(null);
        return;
    }
    var nodeData = null;
    //var chartDetailsUrl = 'bb.json'; //should be ID!!!
    if (ZipNumber > 0) {
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
  var res = "" ;
    var num = fn.substr("runData".length, (fn.indexOf(".json") - "runData".length));
   var n = parseInt(num,10);
    if(n>=0) {
		var b = parseInt(n/ZipNumber);
		//alert(b);
		++b;
		res= "zipData" + b + ".zip";
    }
   return res;
}


function showDiv(id, isVisible) {
    if (document.getElementById(id) != null) {
        document.getElementById(id).style.visibility = isVisible ? 'visible' : 'hidden';
    }
}

function showLoadingData(bShow) {
    document.getElementById('loading').style.visibility = bShow ? 'visible' : 'hidden';
    document.getElementById('loading').innerHtml =  "";
    document.getElementById('loading').style.height = 0;
    document.getElementById('test_tree_table').style.visibility = bShow ? 'hidden' : 'visible';
    document.getElementById('filter_tree_div').style.visibility = bShow ? 'hidden' : 'visible';
    document.getElementById('table1').style.visibility = bShow ? 'hidden' : 'visible';
    document.getElementById('filter1_div').style.visibility = bShow ? 'hidden' : 'visible';

    //showDiv('table2', !bShow);
    //showDiv('table3', !bShow);
    //showDiv('table4', !bShow);
	//showDiv('table5', !bShow);
    //showDiv('filter2_div', !bShow);
    //showDiv('filter3_div', !bShow);
    //showDiv('filter4_div', !bShow);
	//showDiv('filter5_div', !bShow);
	showDiv('loadingTabs', bShow);


}
function resetRun() {
    load_table($("#table1"), -1, 1, false, 0);
    resetRunsData();
}

function resetRunsData() {
    if (isError) {
        load_table($("#table2"), -1, 1, false, 0);
    }
    if (isWarn) {
        load_table($("#table3"), -1, 1, false, 0)
    }
    if (isProp) {
        load_table($("#table4"), -1, 1, false, 0)
    }
	if (isFault) {
        load_table($("#table5"), -1, 1, false, 0)
    }
}


var emptyData = [
    {"a": "  ", "title": "   ", "lazy": false, "folder": false}
];

var runData = null;
var errorData = null;
var warnData = null;
var propData = null;
var faultData = null;

var RUN = 1;
var ERROR = 2;
var WARN = 3;
var PROP = 4;
var FAULT = 5;


function showNodeData(nodeData) {
    showLoadingData(false);
    if (nodeData == null || nodeData == undefined || nodeData.length == 0) {
        return;
    }
    runData = nodeData.run_items;
    showRunsTable();

}


function getDataByType(type) {
    switch (type) {
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
        default:
            return emptyData;
    }
}

var currentType = null;
function load_table(tab, dataType, title_index, isTerm, ident, actFunc) {
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
        activate: actFunc == undefined ? function (event, data) {
        } : actFunc,
        lazyLoad: function (event, data) {
            data.result = {url: "lazy.json"};
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
function showRunsTable() {
    resetRunsData();
    load_table($("#table1"), RUN, table1_title_index, false, 0, loadRunsData);
    var tree_table = $("#table1").fancytree("getTree");

    //filter
    implementFilter($("input[name=search1]"), $("button#btnResetSearch1"), $("span#matches1"), tree_table);
}


function loadRunsData(event, data) {
    showDiv('loadingTabs', true);
    resetRunsData();
    if (isError) {
        if (data.node.data.errors_items === undefined) {
            errorData = emptyData;
        } else {
            errorData = data.node.data.errors_items;
        }
        showErrors();
    }
    if (isWarn) {
        if (data.node.data.warn_items === undefined) {
            warnData = emptyData
        } else {
            warnData = data.node.data.warn_items;
        }
        showWarn();
    }
    if (isProp) {
        if (data.node.data.properties_items === undefined) {
            propData = emptyData
        } else {
            propData = data.node.data.properties_items;
        }
        showProp();
    }
	if (isFault) {
        if (data.node.data.faults_items === undefined) {
            faultData = emptyData
        } else {
            faultData = data.node.data.faults_items;
        }
        showFault();
    }
    showDiv('loadingTabs', false);
}

function showErrors() {
    load_table($("#table2"), ERROR, table2_title_index, false, 0);
    var tree_table = $("#table2").fancytree("getTree");

    //filter
    implementFilter($("input[name=search2]"), $("button#btnResetSearch2"), $("span#matches2"), tree_table);
}

function showWarn() {
    load_table($("#table3"), WARN, table3_title_index, false, 0);
    var tree_table = $("#table3").fancytree("getTree");

    //filter
    implementFilter($("input[name=search3]"), $("button#btnResetSearch3"), $("span#matches3"), tree_table);
}

function showProp() {
    load_table($("#table4"), PROP, table4_title_index, false, 0);
    var tree_table4 = $("#table4").fancytree("getTree");

    //filter
    implementFilter($("input[name=search4]"), $("button#btnResetSearch4"), $("span#matches4"), tree_table4);
}



function showFault() {
    load_table($("#table5"), FAULT, table4_title_index, false, 0);
    var tree_table4 = $("#table5").fancytree("getTree");

    //filter
    //implementFilter($("input[name=search4]"), $("button#btnResetSearch4"), $("span#matches4"), tree_table4);
}
function showTree(input) {
    // Attach the fancytree widget to an existing <div id="tree"> element
    // and pass the tree options as an argument to the fancytree() function:

    $("#test_tree_table").fancytree({
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
            loadFile(data.node.data.test_data);
        },

        lazyLoad: function (event, data) {
            data.result = {url: "lazy.json"};
        },

        table: {
            indentation: 20,      // indent 20px per node level
            nodeColumnIdx: table_tree_title_column_number     // render the node title into the 0nd column
            //checkboxColumnIdx: 0  // render the checkboxes into the 1st column
        },

        renderColumns: function (event, data) {
            getCell(event, data, table_tree_title_column_number);

        },
        icons: false, // Display node icons.
        focusOnSelect: true,
        postProcess: function (event, data) {
            showLoadingData(false);
        }
    });

    var tree_table = $("#test_tree_table").fancytree("getTree");

    //filter
    implementFilter($("input[name=search_test_tree]"), $("button#btnResetSearch_test_tree"), $("span#matches_test_tree"), tree_table);
//    myLayout1.sizePane("west", .5);


}





