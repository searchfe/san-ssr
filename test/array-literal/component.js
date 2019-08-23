const san = require('san')
const List = san.defineComponent({
    template: '<ul><li s-for="item in list">{{item}}</li></ul>'
})

const MyComponent = san.defineComponent({
    components: {
        'x-l': List
    },
    template: '<div><x-l list="{{[1, true, ...ext, \'erik\', ...ext2]}}"/></div>'
})

exports = module.exports = MyComponent
