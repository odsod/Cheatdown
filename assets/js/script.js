(function ($) {
  $(function () {
    setTimeout(function () {
      $('h1, h2, h3, h4, h5, h6').addClass('dontend');
      $('#container').columnize({ columns: 8 });
    }, 1000);
    setTimeout(function () { console.log('blubb!'); }, 2000);
    prettyPrint();
    $(window).resize();
  });
}(jQuery));
