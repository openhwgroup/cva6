function toggleLiveResizing() {
    $.each($.layout.config.borderPanes, function (i, pane) {
        var o = myLayout.options[ pane ];
        o.livePaneResizing = !o.livePaneResizing;
    });
};

function toggleStateManagement(skipAlert, mode) {
    if (!$.layout.plugins.stateManagement) return;

    var options = myLayout.options.stateManagement
        , enabled = options.enabled // current setting
        ;
    if ($.type(mode) === "boolean") {
        if (enabled === mode) return; // already correct
        enabled = options.enabled = mode
    }
    else
        enabled = options.enabled = !enabled; // toggle option

    if (!enabled) { // if disabling state management...
        myLayout.deleteCookie(); // ...clear cookie so will NOT be found on next refresh
        if (!skipAlert)
            alert('This layout will reload as the options specify \nwhen the page is refreshed.');
    }
    else if (!skipAlert)
        alert('This layout will save & restore its last state \nwhen the page is refreshed.');


};

// set EVERY 'state' here so will undo ALL layout changes
// used by the 'Reset State' button: myLayout.loadState( stateResetSettings )
/*
 var stateResetSettings = {
 north__size:		"auto"
 ,	north__initClosed:	false
 ,	north__initHidden:	false
 ,	south__size:		"auto"
 ,	south__initClosed:	false
 ,	south__initHidden:	false
 ,	west__size:			200
 ,	west__initClosed:	false
 ,	west__initHidden:	false
 ,	east__size:			300
 ,	east__initClosed:	false
 ,	east__initHidden:	false
 };
 */

var tabLayoutOptions = {

    resizeWithWindow: true // *** IMPORTANT *** tab-layouts must NOT resize with the window
    , center__contentSelector: ".ui-widget-content",east__size:.5, west__size:.5, north__size:.5, north__togglerLength_closed: '100%' // toggle-button is full-width of resizer-bar
    , north__initClosed: false, north__initHidden: false, sliderCursor: "pointer", togglerTip_open: 'Open', togglerTip_open: 'Close', fxName: 'slide'
    //, spacing_open: 10
    , onresize: function (evt, ui) {
        $.layout.callbacks.resizeTabLayout(evt, ui);
    }

};
var myLayout;
var $Tabs;
var blockLayout = null;
var statementLayout = null;
var subToggleLayout = null;
var expLayout;
var subExpLayout;
var toggleLayout;
var fsmLayout;
var fsmSubLayout
var coverLayout;
var runLayout;
var runSubLayout;
var faultLayout;


function resizeRightTabs() {
    //$Tabs.layout().resizeAll();

    //Resize the left pannel, but ONLY the tab that is active - Mandatory
    var active = $("#tabs").tabs("option", "active");
    var chosenTab = $("#tabs ul>li a").eq(active).attr('href');

    if (chosenTab == '#toggleTab') {
        toggleLayout.resizeAll();
        if(isVplan === true) {
            subToggleLayout.resizeAll();
        }
    } else if (chosenTab == '#expressionTab') {

        expLayout.resizeAll();
        subExpLayout.resizeAll();

    } else if (chosenTab == '#fsmTab') {

        fsmLayout.resizeAll();
        fsmSubLayout.resizeAll();

    } else if (chosenTab == '#coverTab') {

        coverLayout.resizeAll();
        // coverSubLayout.resizeAll();

    } else if (chosenTab == '#blockTab' && isVplan === true) {

        blockLayout.resizeAll();
        // coverSubLayout.resizeAll();

    } else if (chosenTab == '#statementTab' && isVplan === true) {

        statementLayout.resizeAll();
        // coverSubLayout.resizeAll();

    }   else if (chosenTab == '#runTab' && isVplan === true) {

            runLayout.resizeAll();
            runSubLayout.resizeAll();
            // coverSubLayout.resizeAll();

    } // else if (isVplan === false && chosenTab == '#faultTab') {
        //faultLayout.resizeAll();
    //}


}


function initUI() {

    resetTabs();
    $("#tabs").tabs({ disabled: true });
    if(isRecursive) {
        loadFile("covData.json") ;

    }  else {

        document.getElementById('treetable').style.visibility = 'hidden';
        document.getElementById('loading').style.visibility = 'visible';

        diff("tree.json");
    }
}

var layoutSettings = {

    //	reference only - these options are NOT required because 'true' is the default
    closable: true	// pane can open & close
    , resizable: true	// when open, pane can be resized
    , slidable: true	// when closed, pane can 'slide' open over other panes - closes on mouse-out
    , livePaneResizing: true

    //	some resizing/toggling settings

    //	,	south__resizable:			false	// OVERRIDE the pane-default of 'resizable=true'
    //	,	south__spacing_open:		0		// no resizer-bar when open (zero height)
    //	,	south__spacing_closed:		20		// big resizer-bar when open (zero height)
    , south__minSize: 100, south__size: 200	// 'fast' animation when resizing west-pane


    //	some pane-size settings
    , west__minSize: 100, east__size: .5, west__size: .5, east__minSize: 100
    //	,	east__maxSize:				.5 // 50% of layout width
    , center__minWidth: 100, center__size: .5

    //	some pane animation settings
//		,	west__animatePaneSizing:	false
    , west__fxSpeed_size: "fast"	// 'fast' animation when resizing west-pane
    , west__fxSpeed_open: 700	// 1-second animation when opening west-pane
    //	,	west__fxSettings_open:		{ easing: "easeOutBounce" } // 'bounce' effect when opening
    //	,	west__fxName_close:			"none"	// NO animation when closing west-pane

    //	enable showOverflow on west-pane so CSS popups will overlap north pane
//		,	west__showOverflowOnHover:	true

    //	enable state management
    , stateManagement__enabled: true // automatic cookie load & save enabled by default
	,north: {
				size:				300
			,	resizable:			false
			,	togglerLength_open:	0
			,	spacing_open:		1 /* cosmetic only */
			,	initHidden:			true
			,	onhide_end:			function () {
					$("#pane4-open").slideDown();
					$("#pane4-closed").hide();
				}
			,	onshow_start:		function () {
					$("#pane4-open").hide();
					$("#pane4-closed").slideDown();
				}
	}

    , showDebugMessages: true // log and/or display messages from debugging & testing code
    , onresize: function (evt, ui) {
        resizeRightTabs();
    }
};


$(document).ready(function () {
    // create the tabs before the page layout because tabs will change the height of the north-pane
    //$( "#tabs" ).tabs();
    $Tabs = $("#tabs").tabs({
        //activate: $.layout.callbacks.resizeTabLayout,
        activate: function (evt, ui) {
            // resize inner tab-layout(s), if are any
            $.layout.callbacks.resizeTabLayout(evt, ui);

            var active = $("#tabs").tabs("option", "active");
            var chosenTab = $("#tabs ul>li a").eq(active).attr('href');
            //loadTab(chosenTab);
        },
        create: function (evt, ui) {
            // create the layout inside all tabs //setTimeout if I'll have sync problems!!!!
            if (EXPRESSION_TAB_INDEX >= 0) {

                expLayout = $("#expressionTab").layout(tabLayoutOptions);
                subExpLayout = $('#expressionTab > .ui-layout-center').layout(tabLayoutOptions);
            }
            if (TOGGLE_TAB_INDEX >= 0) {
                toggleLayout = $("#toggleTab").layout(tabLayoutOptions);
                if(isVplan === true) {
                    subToggleLayout = $('#toggleTab > .ui-layout-center').layout(tabLayoutOptions);
                }
            }
            if (FSM_TAB_INDEX >= 0) {
                fsmLayout = $("#fsmTab").layout(tabLayoutOptions);
                fsmSubLayout = $('#fsmTab > .ui-layout-center').layout(tabLayoutOptions);
            }
            if (COVER_TAB_INDEX >= 0) {
                coverLayout = $("#coverTab").layout(tabLayoutOptions);
                //coverSubLayout = $('#coverTab > .ui-layout-center').layout(tabLayoutOptions);
            }

            if (BLOCK_TAB_INDEX >= 0 && isVplan === true) {
                blockLayout = $("#blockTab").layout(tabLayoutOptions);

            }
            if (STATEMENT_TAB_INDEX >= 0 && isVplan === true) {
                statementLayout = $("#statementTab").layout(tabLayoutOptions);

            }

            if ( isVplan === true && RUN_TAB_INDEX >= 0 ) {
                runLayout = $("#runTab").layout(tabLayoutOptions);
                runSubLayout = $('#runTab > .ui-layout-center').layout(tabLayoutOptions);

            }

          //  if (isVplan === false && FAULT_TAB_INDEX >= 0) {
          //      faultLayout = $("#faultTab").layout(tabLayoutOptions);
          //  }

        },
        remove: function (evt, ui) {
            // resize tabs-layout in case tabs no longer wrapped to another line
            $Tabs.layout().resizeAll();
        }

    });

    // this layout could be created with NO OPTIONS - but showing some here just as a sample...
    // myLayout = $('body').layout(); -- syntax with No Options

    //myLayout = $('body').layout(layoutSettings);
	myLayout = $("body > #container > #content").layout(layoutSettings);

    // if there is no state-cookie, then DISABLE state management initially
    var cookieExists = !$.isEmptyObject(myLayout.readCookie());
    if (!cookieExists) toggleStateManagement(true, false);


    /*
     *	DISABLE TEXT-SELECTION WHEN DRAGGING (or even _trying_ to drag!)
     *	this functionality will be included in RC30.80
     */
    $.layout.disableTextSelection = function () {
        var $d = $(document)
            , s = 'textSelectionDisabled'
            , x = 'textSelectionInitialized'
            ;
        if ($.fn.disableSelection) {
            if (!$d.data(x)) // document hasn't been initialized yet
                $d.on('mouseup', $.layout.enableTextSelection).data(x, true);
            if (!$d.data(s))
                $d.disableSelection().data(s, true);
        }
        //console.log('$.layout.disableTextSelection');
    };
    $.layout.enableTextSelection = function () {
        var $d = $(document)
            , s = 'textSelectionDisabled';
        if ($.fn.enableSelection && $d.data(s))
            $d.enableSelection().data(s, false);
        //console.log('$.layout.enableTextSelection');
    };
    $(".ui-layout-resizer")
        .disableSelection() // affects only the resizer element
        .on('mousedown', $.layout.disableTextSelection); // affects entire document

    //myLayout.sizePane("north", 145);
    if(!isRecursive)
        myLayout.sizePane("west", .3);


    // if a theme is applied by ThemeSwitch *onLoad*, it may change the height of some content,
    // so we need to call resizeLayout to 'correct' any header/footer heights affected
    // call multiple times so fast browsers update quickly, and slower ones eventually!
    // NOTE: this is only necessary because we are changing CSS *AFTER LOADING* (eg: themeSwitcher)
    setTimeout(myLayout.resizeAll, 10);
    setTimeout(myLayout.resizeAll, 1000);
    /* allow time for browser to re-render for theme */
    setTimeout(myLayout.resizeAll, 5000);
    /* for really slow browsers */

    if(!isRecursive){
        document.getElementById('loading').style.visibility = 'visible';
        document.getElementById('treetable').style.visibility = 'hidden';
        diff("tree.json");
    } else {
        loadFile("covData.json");
    }
    //document.getElementById('filter_div').style.visibility = 'hidden';





});



