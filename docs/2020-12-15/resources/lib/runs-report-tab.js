function toggleLiveResizing() {
    $.each($.layout.config.borderPanes, function (i, pane) {
        var o = myLayout.options[pane];
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

var tabLayoutOptions = {

    resizeWithWindow: true // *** IMPORTANT *** tab-layouts must NOT resize with the window
    ,
    center__contentSelector: ".ui-widget-content",
    east__size: .5,
    west__size: .5,
    north__size: .5,
    north__togglerLength_closed: '100%' // toggle-button is full-width of resizer-bar
    ,
    north__initClosed: false,
    north__initHidden: false,
    sliderCursor: "pointer",
    togglerTip_open: 'Open',
    togglerTip_open: 'Close',
    fxName: 'slide'
    //, spacing_open: 10
    ,
    onresize: function (evt, ui) {
        $.layout.callbacks.resizeTabLayout(evt, ui);
    }

};
var isGrouped = -1;
var myLayout;
var myLayout1;
var $Tabs;
;


function diff_table(input, id, indx) {

        // Attach the fancytree widget to an existing <div id="tree"> element
        // and pass the tree options as an argument to the fancytree() function:
        try {
            $(id).fancytree({
                extensions: ["table", "filter"],
                quicksearch: true,
                checkbox: false,
                filter: {
                    mode: "hide",
                    autoApply: true
                },
                source: {
                    url: input,
                    cache: true
                },

                lazyLoad: function (event, data) {
                    data.result = {url: "lazy.json"};
                },

                table: {
                    indentation: 0,      // indent 20px per node level
                    nodeColumnIdx: indx   // render the node title into the 0nd column
                    //checkboxColumnIdx: 0  // render the checkboxes into the 1st column
                },

                renderColumns: function (event, data) {
                    getCell(event, data, indx);

                },
                postProcess: function (event, data) {
                },
                icons: false, // Display node icons.
                focusOnSelect: true

            });
        } catch (e) {

        }
    }

function resizeRightTabs() {
   // $Tabs.layout().resizeAll();

    //Resize the left pannel, but ONLY the tab that is active - Mandatory
    var active = $("#tabs").tabs("option", "active");
    var chosenTab = $("#tabs ul>li a").eq(active).attr('href');

    // if (chosenTab == '#errorTab') {
        // errorLayout.resizeAll();
    // } else if (chosenTab == '#warnTab') {
        // warnLayout.resizeAll();
    // } else if (chosenTab == '#propTab') {
        // propLayout.resizeAll();
    // } else if (chosenTab == '#faultTab') {
        // faultLayout.resizeAll();
    // }
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
    , north: {
        size: 300
        , resizable: false
        , togglerLength_open: 0
        , spacing_open: 1 /* cosmetic only */
        , initHidden: true
        , onhide_end: function () {
            $("#pane4-open").slideDown();
            $("#pane4-closed").hide();
        }
        , onshow_start: function () {
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
            if (ERROR_TAB_INDEX >= 0) {
              //  erroLayout = $("#errorTab").layout(tabLayoutOptions);
            }
            if (WARN_TAB_INDEX >= 0) {
             //   warnLayout = $("#warnTab").layout(tabLayoutOptions);
            }
            if (PROP_TAB_INDEX >= 0) {
             //   propLayout = $("#propTab").layout(tabLayoutOptions);
            }
            if (FAULT_TAB_INDEX >= 0) {
               // faultLayout = $("#faultTab").layout(tabLayoutOptions);
            }
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
	if(isGrouped > 0) {
        myLayout1 = $('body  > #container > #content > .ui-layout-west').layout(layoutSettings);
    }

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
    myLayout.sizePane("west", .5);
    if(myLayout1 != undefined) {
        myLayout1.sizePane("west", .5);
    }


    // if a theme is applied by ThemeSwitch *onLoad*, it may change the height of some content,
    // so we need to call resizeLayout to 'correct' any header/footer heights affected
    // call multiple times so fast browsers update quickly, and slower ones eventually!
    // NOTE: this is only necessary because we are changing CSS *AFTER LOADING* (eg: themeSwitcher)
    setTimeout(myLayout.resizeAll, 5000);
    if(myLayout1 != undefined) {
        setTimeout(myLayout1.resizeAll, 5000);
    }
    /* for really slow browsers */



        $("#tabs").tabs({disabled: false});
        initUI();






});



